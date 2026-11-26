-- Prove2me | solution 1 for MohP3.C18_mul_18K
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:02:47.311709+00:00
-- url     : https://prove2.me/submissions/6253bde3-b6fe-44f7-9671-85a7cd020abb

module
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_IndependenceK
public import Definitions.Def_MohP3_GlobalK

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3
theorem _root_.solution : (MvPolynomial.C ((18 : k)⁻¹) : Rk k) * (18 : Rk k) = 1 := by
  have h18 : (18 : k) ≠ 0 := by norm_num
  rw [show (18 : Rk k) = MvPolynomial.C (18 : k) from (map_ofNat MvPolynomial.C 18).symm,
    ← map_mul, inv_mul_cancel₀ h18, map_one]
end MohP3
