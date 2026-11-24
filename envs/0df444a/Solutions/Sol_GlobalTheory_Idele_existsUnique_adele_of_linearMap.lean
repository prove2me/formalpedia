-- Prove2me | solution 1 for GlobalTheory.Idele.existsUnique_adele_of_linearMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:29:49.24186+00:00
-- url     : https://prove2.me/submissions/d3d32d36-867b-4faf-8330-4c2295bd4237

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Idele_exists_adele_of_linearMap
import Theorems.Thm_GlobalTheory_Idele_eq_zero_of_forall_mul_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk

set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped nonZeroDivisors IsDedekindDomain.FiniteAdeleRing
noncomputable section
open GlobalTheory GlobalTheory.Idele
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace GlobalTheory.Idele
theorem _root_.solution {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (φ : (K ⧸ (I : Submodule R K)) →ₗ[R] (K ⧸ (J : Submodule R K))) :
    ∃! t : 𝔸ᶠ[R, K], ∀ x : K, quotEquivAdelic hJ (φ (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk (t * algebraMap K 𝔸ᶠ[R, K] x) := by
  obtain ⟨t, ht⟩ := exists_adele_of_linearMap hI hJ
    ((quotEquivAdelic hJ).toLinearMap ∘ₗ φ ∘ₗ (quotEquivAdelic hI).symm.toLinearMap)
  have ht' : ∀ x : K, quotEquivAdelic hJ (φ (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk (t * algebraMap K 𝔸ᶠ[R, K] x) := fun x => by
    rw [← ht, ← quotEquivAdelic_mk hI]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  refine ⟨t, ht', fun s hs => ?_⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_mul_mem hJ fun x => ?_
  rw [sub_mul, ← Submodule.Quotient.eq, ← hs, ← ht']
end GlobalTheory.Idele
