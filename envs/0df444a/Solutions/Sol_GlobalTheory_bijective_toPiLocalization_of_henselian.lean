-- Prove2me | solution 1 for GlobalTheory.bijective_toPiLocalization_of_henselian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:39:44.181153+00:00
-- url     : https://prove2.me/submissions/71e89e1c-5887-4610-9eda-8452a7558587

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Theorems.Thm_GlobalTheory_finite_maximalSpectrum_of_finite_of_isLocalRing
import Theorems.Thm_GlobalTheory_exists_completeOrthogonalIdempotents_of_henselian
import Theorems.Thm_GlobalTheory_surjective_algebraMap_localization_of_henselian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct
namespace GlobalTheory
theorem _root_.solution (R S : Type*) [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S] :
    Function.Bijective (MaximalSpectrum.toPiLocalization S) := by
  classical
  refine ⟨MaximalSpectrum.toPiLocalization_injective S, fun y ↦ ?_⟩
  have := finite_maximalSpectrum_of_finite_of_isLocalRing R S
  have := Fintype.ofFinite (MaximalSpectrum S)
  obtain ⟨e, he, H⟩ := exists_completeOrthogonalIdempotents_of_henselian R S
  choose a ha using fun q : MaximalSpectrum S ↦
    have := q.isMaximal; surjective_algebraMap_localization_of_henselian R q.asIdeal (y q)
  have h1 : ∀ q : MaximalSpectrum S, algebraMap S (Localization.AtPrime q.asIdeal) (e q) = 1 :=
    fun q ↦ (IsIdempotentElem.iff_eq_one_of_isUnit (IsLocalization.map_units _
      (⟨e q, (H q _ q.isMaximal).2 rfl⟩ : q.asIdeal.primeCompl))).1 ((he.idem q).map _)
  refine ⟨∑ q, e q * a q, funext fun q ↦ ?_⟩
  rw [MaximalSpectrum.toPiLocalization_apply_apply, map_sum, Finset.sum_eq_single q]
  · rw [map_mul, h1, one_mul, ha]
  · intro p _ hpq
    have := congr(algebraMap S (Localization.AtPrime q.asIdeal) $(he.ortho hpq))
    rw [map_mul, h1, mul_one, map_zero] at this
    rw [map_mul, this, zero_mul]
  · simp
end GlobalTheory
