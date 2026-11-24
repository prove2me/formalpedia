-- Prove2me | solution 1 for GlobalTheory.norm_hasSum_eq_of_dominant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:27:15.340704+00:00
-- url     : https://prove2.me/submissions/fa23886e-113e-4172-b6e6-a82f05e4b2d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormHasSumEqOfDominant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type)
    (f : ι → K) (s : K) (i₀ : ι), HasSum f s → (∀ i, i ≠ i₀ → ‖f i‖ < ‖f i₀‖) → ‖s‖ = ‖f i₀‖ := by
  intro K _ _ ι f s i₀ hsum h
  classical
  have hs : Summable f := hsum.summable
  have hf : Filter.Tendsto f Filter.cofinite (nhds 0) := hs.tendsto_cofinite_zero
  rw [← hsum.tsum_eq, hs.tsum_eq_add_tsum_ite i₀]
  by_cases h0 : f i₀ = 0
  · have : ∀ i, (if i = i₀ then 0 else f i) = 0 := by
      intro i
      split_ifs with hi
      · rfl
      · have := h i hi
        rw [h0, norm_zero] at this
        exact absurd this (norm_nonneg _).not_gt
    simp [this]
  have hc : 0 < ‖f i₀‖ := norm_pos_iff.2 h0
  set g : ι → K := fun i => if i = i₀ then 0 else f i with hg
  have hglt : ∀ i, ‖g i‖ < ‖f i₀‖ := by
    intro i
    simp only [hg]
    split_ifs with hi
    · simpa using hc
    · exact h i hi
  have hfin : {i | ¬ ‖f i‖ < ‖f i₀‖ / 2}.Finite := by
    have := (NormedAddCommGroup.tendsto_nhds_zero.1 hf) (‖f i₀‖ / 2) (by positivity)
    exact Filter.eventually_cofinite.1 this
  obtain ⟨j, -, hj⟩ := Set.exists_max_image _ (fun i => ‖g i‖) hfin
    ⟨i₀, by simp only [Set.mem_setOf_eq]; linarith⟩
  have hb : ‖∑' i, g i‖ ≤ max (‖f i₀‖ / 2) ‖g j‖ := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun i => ?_
    by_cases hi : ‖f i‖ < ‖f i₀‖ / 2
    · refine le_max_of_le_left ?_
      simp only [hg]
      split_ifs
      · simp only [norm_zero]; positivity
      · exact hi.le
    · exact le_max_of_le_right (hj i hi)
  have hlt : ‖∑' i, g i‖ < ‖f i₀‖ := hb.trans_lt (max_lt (by linarith) (hglt j))
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]
end GlobalTheory
