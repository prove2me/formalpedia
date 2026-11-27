-- Prove2me | solution 1 for MohP3.HilbertBurch.span_fvec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:39:16.050569+00:00
-- url     : https://prove2.me/submissions/dbecf526-3097-4d8d-bebf-4e78327a088a

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch
public import Theorems.Thm_MohP3_HilbertBurch_range_fvec

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open MohP3 MohP3.HilbertBurch
open Matrix
open MvPolynomial
variable {A : Type*} [CommRing A]
namespace MohP3.HilbertBurch
theorem _root_.solution (x y z : A) : Ideal.span (Set.range (fvec x y z)) = Gen.P x y z := by
  rw [range_fvec]; rfl
end MohP3.HilbertBurch
