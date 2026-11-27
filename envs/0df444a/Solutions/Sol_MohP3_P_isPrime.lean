-- Prove2me | solution 1 for MohP3.P_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:22:58.063512+00:00
-- url     : https://prove2.me/submissions/2e9cdf55-4cf8-45f0-bcb9-9fe738974e44

module
public import Definitions.Def_MohP3_Kernel
public import Definitions.Def_MohP3_Global
public import Theorems.Thm_MohP3_kernel_rho


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution : P.IsPrime := kernel_rho ▸ RingHom.ker_isPrime rho
end MohP3
