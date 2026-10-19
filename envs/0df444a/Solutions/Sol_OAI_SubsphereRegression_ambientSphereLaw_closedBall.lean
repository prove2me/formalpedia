-- Prove2me | solution 1 for OAI.SubsphereRegression.ambientSphereLaw_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:00:48.092837+00:00
-- url     : https://prove2.me/submissions/a7f5f1dd-7b5c-473d-ba66-56cf79390061

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Regression/Spheres.lean:L137-L156
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereRegression.ambientSphereLaw_closedBall. The node keeps its source
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
import Theorems.Thm_OAI_SubsphereRegression_sphereLaw_cap_raw

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

lemma ambientSphereLaw_closedBall [Nontrivial E] (z : E) {r : ℝ} (hr : 0 < r)
    (k : ℕ) (hk : k ≤ Module.finrank ℝ E - 1) :
    ambientSphereLaw (Metric.closedBall z r) ≤
      ENNReal.ofReal ((3 : ℝ) * 4 ^ Module.finrank ℝ E) * ENNReal.ofReal (r^k) := by
  by_cases hr1 : r ≤ 1
  · rw [ambientSphereLaw, Measure.map_apply (by fun_prop) Metric.isClosed_closedBall.measurableSet]
    apply (sphereLaw_cap_raw z hr hr1 (Module.finrank_pos (R := ℝ) (M := E))).trans
    apply mul_le_mul' le_rfl
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hr.le hr1 hk)
  · have hr1 : 1 ≤ r := (le_of_not_ge hr1)
    calc
      _ ≤ 1 := prob_le_one
      _ ≤ _ := by
        apply one_le_mul
        · rw [← ENNReal.ofReal_one]
          apply ENNReal.ofReal_le_ofReal
          have : (1 : ℝ) ≤ 4 ^ Module.finrank ℝ E := one_le_pow₀ (by norm_num)
          linarith
        · rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (one_le_pow₀ hr1)

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


theorem solution : type_of% @_root_.OAI.SubsphereRegression.ambientSphereLaw_closedBall := @_root_.OAI.SubsphereRegression.ambientSphereLaw_closedBall
