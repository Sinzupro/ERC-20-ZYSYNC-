import { Wallet, utils } from "zksync-web3";
import * as ethers from "ethers";
import { HardhatRuntimeEnvironment } from "hardhat/types";
import { Deployer } from "@matterlabs/hardhat-zksync-deploy";

const fs = require('fs');
const privateKey = fs.readFileSync('.secret').toString().trim();
// An example of a deploy script that will deploy and call a simple contract.
export default async function (hre: HardhatRuntimeEnvironment) {
  console.log(`Running deploy script for the Goat contract`);

  // Initialize the wallet.
  const wallet = new Wallet(privateKey);

  // Create deployer object and load the artifact of the contract you want to deploy.
  const deployer = new Deployer(hre, wallet);
  const artifact = await deployer.loadArtifact("GOAT");

   // Estimate contract deployment fee
   const deploymentFee = await deployer.estimateDeployFee(artifact, []);

    // Deploy this contract. The returned object will be of a `Contract` type, similarly to ones in `ethers`.
  // `greeting` is an argument for contract constructor.
  const parsedFee = ethers.utils.formatEther(deploymentFee.toString());
  console.log(`The deployment is estimated to cost ${parsedFee} ETH`);

  // Estimate contract deployment fee
  const goatContract = await deployer.deploy(artifact);

//obtain the Constructor Arguments
console.log("constructor args:" + goatContract.interface.encodeDeploy());
  // Show the contract info.
  const contractAddress = goatContract.address;
  console.log(`${artifact.contractName} was deployed to ${contractAddress}`);
}