-- Prove2me | solution 1 for MohP3.Ppoly_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:36:03.920277+00:00
-- url     : https://prove2.me/submissions/27276c8c-ce42-44a0-b87b-d6dcdd8ecebc

module
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_IndependenceK
public import Definitions.Def_MohP3_GlobalK
public import Theorems.Thm_MohP3_global_kernel_k

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3
theorem _root_.solution : (Ppoly k).IsPrime := global_kernel_k k ▸ RingHom.ker_isPrime (rho_k k)
end MohP3
