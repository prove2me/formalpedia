-- Prove2me | solution 1 for MohP3.HilbertBurch.range_genMap_eq_J
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:42:03.748968+00:00
-- url     : https://prove2.me/submissions/3e98a010-3555-4825-af70-a61cc38b5f15

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch
public import Theorems.Thm_MohP3_HilbertBurch_range_rowMap

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
theorem _root_.solution : LinearMap.range (genMap k) = J k := by
  have := range_rowMap (A := S k) (X 0) (X 1) (X 2)
  exact this
end MohP3.HilbertBurch
