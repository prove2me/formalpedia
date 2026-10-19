-- Prove2me | solution 1 for OAI.NoiselessRegression.card_le_volume_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T18:56:05.025329+00:00
-- url     : https://prove2.me/submissions/09c758fb-7e3c-4d6e-ac41-044fc7c78f91

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Nets.lean:L44-L84
-- (upload_full_project.md Phase 4): solution for node OAI.NoiselessRegression.card_le_volume_ratio. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments

-- ---- from OAI.Probability.GaussianRegression.Nets ----
namespace OAI

/-!
Local mass bounds and quantitative finite Euclidean nets.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section

universe u

namespace NoiselessRegression

section FrostmanGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem card_le_volume_ratio (s : Finset E) {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hs : ∀ x ∈ s, ‖x‖ ≤ R)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ dist x y) :
    (s.card : ℝ) ≤ ((R + r / 2) / (r / 2)) ^ Module.finrank ℝ E := by
  classical
  let ν : Measure E := Measure.addHaar
  let δ : ℝ := r / 2
  let ρ : ℝ := R + r / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let A : Set E := ⋃ c ∈ s, Metric.ball c δ
  have hd : Set.Pairwise (s : Set E) (fun c d => Disjoint (Metric.ball c δ) (Metric.ball d δ)) := by
    intro c hc d hd hcd
    apply Metric.ball_disjoint_ball
    simpa [δ] using hsep c hc d hd hcd
  have hsub : A ⊆ Metric.ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ?_
    apply Metric.ball_subset_ball'
    dsimp [δ, ρ]
    rw [dist_zero_right]
    linarith [hs x hx]
  have I :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ E) * ν (Metric.ball 0 1) ≤
        ENNReal.ofReal (ρ ^ Module.finrank ℝ E) * ν (Metric.ball 0 1) := by
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ E) * ν (Metric.ball 0 1) = ν A := by
        dsimp only [A]
        rw [measure_biUnion_finset hd (fun _ _ => Metric.isOpen_ball.measurableSet)]
        simp only [ν.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ ν (Metric.ball (0 : E) ρ) := measure_mono hsub
      _ = _ := ν.addHaar_ball_of_pos 0 hρ
  have J : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ E) ≤
      ENNReal.ofReal (ρ ^ Module.finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (Metric.measure_ball_pos ν 0 zero_lt_one).ne'
      measure_ball_lt_top.ne).mp I
  have K : (s.card : ℝ) * δ ^ Module.finrank ℝ E ≤ ρ ^ Module.finrank ℝ E := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg hδ.le _)] using
      ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) J
  rw [div_pow]
  exact (le_div_iff₀ (pow_pos hδ _)).mpr K

end FrostmanGeometry

section FiniteNets

variable {E : Type*} [PseudoMetricSpace E]

end FiniteNets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end NoiselessRegression

end

end OAI

-- ---- platform node ----
open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.NoiselessRegression.card_le_volume_ratio := @_root_.OAI.NoiselessRegression.card_le_volume_ratio
