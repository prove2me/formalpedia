-- Prove2me | solution 1 for MohP3.HilbertBurch.hilbertBurch_exact_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:47:39.723323+00:00
-- url     : https://prove2.me/submissions/d62a89e4-0657-4230-bd25-3efc5f0aec21

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch
public import Theorems.Thm_MohP3_HilbertBurch_phiMap_injective
public import Theorems.Thm_MohP3_HilbertBurch_range_phiMap_eq_ker_genMap
public import Theorems.Thm_MohP3_HilbertBurch_range_genMap_eq_J

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
theorem _root_.solution :
    Function.Injective (phiMap k) ∧
      Function.Exact (phiMap k) (genMap k) ∧
      Function.Exact (genMap k) (J k).mkQ ∧
      Function.Surjective (J k).mkQ := by
  refine ⟨phiMap_injective k, ?_, ?_, Submodule.mkQ_surjective _⟩
  · rw [LinearMap.exact_iff]
    exact (range_phiMap_eq_ker_genMap k).symm
  · rw [LinearMap.exact_iff, Submodule.ker_mkQ, range_genMap_eq_J]
end MohP3.HilbertBurch
