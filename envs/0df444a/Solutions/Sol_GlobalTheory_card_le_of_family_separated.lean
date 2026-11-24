-- Prove2me | solution 1 for GlobalTheory.card_le_of_family_separated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:24:50.110937+00:00
-- url     : https://prove2.me/submissions/c970decb-17fa-42f6-a452-38891aba7581

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
open MeasureTheory Metric
namespace GlobalTheory
theorem _root_.solution {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (s : Finset ι) (f : ι → V) {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R)
    (hs : ∀ i ∈ s, ‖f i‖ ≤ R) (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → d ≤ ‖f i - f j‖) :
    (s.card : ℝ) ≤ (1 + 2 * R / d) ^ finrank ℝ V := by
  borelize V
  let μ : Measure V := Measure.addHaar
  have hδ : 0 < d / 2 := by positivity
  have hρ : 0 < R + d / 2 := by positivity
  have D : Set.Pairwise (s : Set ι) (Function.onFun Disjoint fun i => ball (f i) (d / 2)) := by
    intro i hi j hj hij
    apply ball_disjoint_ball
    rw [dist_eq_norm, add_halves]
    exact h i hi j hj hij
  have hsub : (⋃ i ∈ s, ball (f i) (d / 2)) ⊆ ball (0 : V) (R + d / 2) := by
    refine Set.iUnion₂_subset fun i hi => ball_subset_ball' ?_
    rw [dist_zero_right]
    linarith [hs i hi]
  have I : (s.card : ENNReal) * ENNReal.ofReal ((d / 2) ^ finrank ℝ V) * μ (ball 0 1) ≤
      ENNReal.ofReal ((R + d / 2) ^ finrank ℝ V) * μ (ball 0 1) :=
    calc (s.card : ENNReal) * ENNReal.ofReal ((d / 2) ^ finrank ℝ V) * μ (ball 0 1)
        = μ (⋃ i ∈ s, ball (f i) (d / 2)) := by
          rw [measure_biUnion_finset D fun c _ => measurableSet_ball]
          simp only [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : V) (R + d / 2)) := measure_mono hsub
      _ = _ := by simp only [μ.addHaar_ball_of_pos _ hρ]
  have J := (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ _ zero_lt_one).ne'
    measure_ball_lt_top.ne).1 I
  have K := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) J
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_natCast] at K
  have e : 1 + 2 * R / d = (R + d / 2) / (d / 2) := by field_simp; ring
  rw [e, div_pow, le_div_iff₀ (by positivity)]
  exact K
end GlobalTheory
