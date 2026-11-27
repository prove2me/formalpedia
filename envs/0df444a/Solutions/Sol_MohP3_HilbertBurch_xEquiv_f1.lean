-- Prove2me | solution 1 for MohP3.HilbertBurch.xEquiv_f1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:40:13.298798+00:00
-- url     : https://prove2.me/submissions/e39c28de-34d7-4799-a433-90ce64d1f07f

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch
public import Theorems.Thm_MohP3_HilbertBurch_rowMap_apply
public import Theorems.Thm_MohP3_HilbertBurch_xEquiv_X0
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
    (xEquiv (Gen.f1 (X 0) (X 1) (X 2) : MvPolynomial (Fin 3) k)).Monic := by
  simp only [Gen.f1, map_sub, map_add, map_mul, map_pow, map_ofNat, xEquiv_X0, xEquiv_X1,
    xEquiv_X2]
  monicity!
end MohP3.HilbertBurch
