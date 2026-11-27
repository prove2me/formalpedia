-- Prove2me | solution 1 for MohP3.HilbertBurch.hilbertBurch_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:44:53.316781+00:00
-- url     : https://prove2.me/submissions/e81abad3-e452-4b0c-86e5-72e54fe5bcf2

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
      Function.Exact (genMap k) (Ideal.Quotient.mkₐ k (J k)) ∧
      Function.Surjective (Ideal.Quotient.mkₐ k (J k)) := by
  refine ⟨phiMap_injective k, ?_, ?_, Ideal.Quotient.mkₐ_surjective k (J k)⟩
  · rw [LinearMap.exact_iff]
    exact (range_phiMap_eq_ker_genMap k).symm
  · intro w
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Set.mem_range,
      ← LinearMap.mem_range, range_genMap_eq_J]
end MohP3.HilbertBurch
