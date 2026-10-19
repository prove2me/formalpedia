-- Prove2me | solution 1 for OAI.SubsphereRegression.terminal_cap_mass
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:02:25.630607+00:00
-- url     : https://prove2.me/submissions/d26d6fdd-1930-475a-8785-550ed05a3929

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Regression/Spheres.lean:L158-L178
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereRegression.terminal_cap_mass. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Theorems.Thm_OAI_SubsphereRegression_ambientSphereLaw_closedBall

-- ---- from OAI.Probability.Subsphere.Regression.Spheres ----
namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
section SphereBounds
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SphereBounds

open scoped Pointwise
section MoreSphere
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

end MoreSphere

section FubiniAux
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
end FubiniAux

end SubsphereRegression
end
end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
open scoped Topology
open InnerProductSpace
open scoped Pointwise


theorem solution : type_of% @_root_.OAI.SubsphereRegression.terminal_cap_mass := @_root_.OAI.SubsphereRegression.terminal_cap_mass
