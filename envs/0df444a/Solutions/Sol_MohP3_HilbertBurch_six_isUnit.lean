-- Prove2me | solution 1 for MohP3.HilbertBurch.six_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:40:33.549691+00:00
-- url     : https://prove2.me/submissions/625b2fdc-2f68-4791-b241-71555b915996

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch

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
namespace MohP3.HilbertBurch
theorem _root_.solution : IsUnit (6 : MvPolynomial (Fin 3) k) := by
  rw [← map_ofNat (C : k →+* MvPolynomial (Fin 3) k) 6]
  exact (isUnit_iff_ne_zero.mpr (by norm_num)).map C
end MohP3.HilbertBurch
