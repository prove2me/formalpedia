-- Prove2me | solution 1 for GlobalTheory.finset_card_le_of_separated
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:23.62684+00:00
-- url     : https://prove2.me/submissions/99a7da08-0712-4095-9f96-8de0a7347145

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric MeasureTheory Module Set
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
namespace GlobalTheory
theorem _root_.solution (s : Finset E) {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R) (x : E)
    (hs : ∀ a ∈ s, dist a x ≤ R) (hsep : (s : Set E).Pairwise fun a b => d ≤ dist a b) :
    (s.card : ℝ) ≤ (1 + 2 * R / d) ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  have hδ : 0 < d / 2 := by positivity
  have hρ : 0 < R + d / 2 := by positivity
  have D : Set.Pairwise (s : Set E) (Function.onFun Disjoint fun c => ball (c : E) (d / 2)) := by
    intro a ha b hb hab
    exact ball_disjoint_ball (by have := hsep ha hb hab; linarith)
  have hsub : (⋃ c ∈ s, ball (c : E) (d / 2)) ⊆ ball x (R + d / 2) := by
    refine iUnion₂_subset fun a ha => ball_subset_ball' ?_
    have := hs a ha
    linarith
  have I : (s.card : ENNReal) * ENNReal.ofReal ((d / 2) ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal ((R + d / 2) ^ finrank ℝ E) * μ (ball 0 1) := by
    calc (s.card : ENNReal) * ENNReal.ofReal ((d / 2) ^ finrank ℝ E) * μ (ball 0 1)
        = μ (⋃ c ∈ s, ball (c : E) (d / 2)) := by
          rw [measure_biUnion_finset D fun c _ => measurableSet_ball]
          simp only [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball x (R + d / 2)) := measure_mono hsub
      _ = _ := μ.addHaar_ball_of_pos _ hρ
  have J : (s.card : ENNReal) * ENNReal.ofReal ((d / 2) ^ finrank ℝ E) ≤
      ENNReal.ofReal ((R + d / 2) ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 I
  have K : (s.card : ℝ) * (d / 2) ^ finrank ℝ E ≤ (R + d / 2) ^ finrank ℝ E := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top J
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)] at this
  have e : 1 + 2 * R / d = (R + d / 2) / (d / 2) := by field_simp; ring
  rw [e, div_pow, le_div_iff₀ (by positivity)]
  exact K
end GlobalTheory
