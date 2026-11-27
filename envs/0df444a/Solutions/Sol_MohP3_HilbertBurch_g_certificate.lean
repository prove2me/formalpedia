-- Prove2me | solution 1 for MohP3.HilbertBurch.g_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:39:36.755245+00:00
-- url     : https://prove2.me/submissions/cdeebda6-9ff2-4203-aafe-0b7f7ed51920

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch
public import Theorems.Thm_MohP3_HilbertBurch_rowMap_apply
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
namespace MohP3.HilbertBurch
theorem _root_.solution (x y z : A) :
    3 * (y ^ 5 - z ^ 4) = y ^ 2 * Gen.f1 x y z - x * y * Gen.f2 x y z - 3 * z * Gen.f4 x y z := by
  simp only [Gen.f1, Gen.f2, Gen.f4]; ring
end MohP3.HilbertBurch
