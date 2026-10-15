-- Prove2me | solution 1 for OAI.NoiselessRegression.terminal_cap_mass
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:21:58.543721+00:00
-- url     : https://prove2.me/submissions/56eec635-394a-43d1-897a-5854b8e0d898

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Sphere.lean:L159-L179
-- (upload_full_project.md Phase 4): solution for node OAI.NoiselessRegression.terminal_cap_mass. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing
import Definitions.Def_OAI_Probability_GaussianRegression_Projection
import Definitions.Def_OAI_Probability_GaussianRegression_Support
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere
import Theorems.Thm_OAI_NoiselessRegression_ambientSphereLaw_closedBall

-- ---- from OAI.Probability.GaussianRegression.Sphere ----
namespace OAI

/-!
Normalized spherical surface measure, cap bounds, and rotational symmetry.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section SphereBounds
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SphereBounds

open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma terminal_cap_mass [Nontrivial E] (y z : E) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (a : ℕ) (ha : 2*a ≤ Module.finrank ℝ E - 1) :
    ((ambientSphereLaw (E := E)).restrict (Metric.closedBall y ε)) (Metric.closedBall z r) ≤
      ENNReal.ofReal ((3 : ℝ) * 4 ^ Module.finrank ℝ E) *
        ENNReal.ofReal (ε^a) * ENNReal.ofReal (r^a) := by
  rw [Measure.restrict_apply Metric.isClosed_closedBall.measurableSet]
  by_cases h : r ≤ ε
  · apply (measure_mono Set.inter_subset_left).trans
    apply (ambientSphereLaw_closedBall z hr (2*a) ha).trans
    rw [mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hε.le a)]
    apply mul_le_mul' le_rfl
    apply ENNReal.ofReal_le_ofReal
    rw [mul_comm 2 a, pow_mul, pow_two]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le h a) (by positivity)
  · apply (measure_mono Set.inter_subset_right).trans
    apply (ambientSphereLaw_closedBall y hε (2*a) ha).trans
    rw [mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hε.le a)]
    apply mul_le_mul' le_rfl
    apply ENNReal.ofReal_le_ofReal
    rw [mul_comm 2 a, pow_mul, pow_two]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le (le_of_not_ge h) a) (by positivity)

end NoiselessRegression

end

end OAI

-- ---- platform node ----
open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise


theorem solution : type_of% @_root_.OAI.NoiselessRegression.terminal_cap_mass := @_root_.OAI.NoiselessRegression.terminal_cap_mass
