-- Prove2me | solution 1 for MohP3.HilbertBurch.g_eq_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:40:21.371777+00:00
-- url     : https://prove2.me/submissions/3324a476-c9ea-47fe-ae35-c96b253482a0

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch
public import Theorems.Thm_MohP3_HilbertBurch_rowMap_apply
public import Theorems.Thm_MohP3_HilbertBurch_xEquiv_X1
public import Theorems.Thm_MohP3_HilbertBurch_xEquiv_X2
attribute [local simp] MohP3.HilbertBurch.rowMap_apply

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open MohP3 MohP3.HilbertBurch
open Matrix
open MvPolynomial
variable {A : Type*} [CommRing A]
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3.HilbertBurch
theorem _root_.solution :
    (3 * ((X 1) ^ 5 - (X 2) ^ 4) : MvPolynomial (Fin 3) k) =
      xEquiv.symm (Polynomial.C (3 * ((X 0) ^ 5 - (X 1) ^ 4))) := by
  apply xEquiv.injective
  rw [AlgEquiv.apply_symm_apply]
  simp [xEquiv_X1, xEquiv_X2, map_ofNat]
end MohP3.HilbertBurch
