-- Prove2me | solution 1 for GlobalTheory.finset_card_le_of_separated_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:59:45.93314+00:00
-- url     : https://prove2.me/submissions/95c65819-d40f-4db6-9547-b4fd1abd4233

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GaussianSumOfOneSeparatedOfLe
import Theorems.Thm_GlobalTheory_finset_card_le_of_separated


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric MeasureTheory Module Set Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
namespace GlobalTheory
theorem _root_.solution {ι : Type*} (u : ι → E) {r R : ℝ} (hr : 0 < r)
    (hR : 0 ≤ R) (hu : Pairwise fun i j => r ≤ dist (u i) (u j)) (w : E) (s : Finset ι)
    (hs : ∀ i ∈ s, dist (u i) w ≤ R) : (s.card : ℝ) ≤ (1 + 2 * R / r) ^ finrank ℝ E := by
  classical
  have hinj : Function.Injective u := fun i j hij => by
    by_contra hne
    have := hu hne
    simp only [hij, dist_self] at this
    linarith
  rw [← Finset.card_image_of_injective s hinj]
  refine finset_card_le_of_separated _ hr hR w ?_ ?_
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
    exact hs i hi
  · intro a ha b hb hab
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ha)
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
    exact hu fun h => hab (h ▸ rfl)
end GlobalTheory
