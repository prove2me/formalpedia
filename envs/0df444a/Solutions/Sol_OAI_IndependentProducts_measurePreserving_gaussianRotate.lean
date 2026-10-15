-- Prove2me | solution 1 for OAI.IndependentProducts.measurePreserving_gaussianRotate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:08:17.282135+00:00
-- url     : https://prove2.me/submissions/e0f058e2-5af1-4225-b1bd-63744ed22708

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/ScalarBounds.lean:L172-L235
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.measurePreserving_gaussianRotate. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds

-- ---- from OAI.Analysis.ProductSpaces.ScalarBounds ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΩ uι

namespace IndependentProducts

section SecondMoment
variable {Ω : Type uΩ} [MeasurableSpace Ω] {μ : Measure Ω}

variable [IsProbabilityMeasure μ]

end SecondMoment
end IndependentProducts

namespace IndependentProducts

lemma gaussianRotate_measurable : Measurable gaussianRotate := by unfold gaussianRotate; fun_prop

lemma measurePreserving_gaussianRotate : MeasurePreserving gaussianRotate
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  let P := (gaussianReal 0 1).prod (gaussianReal 0 1)
  have hxf : HasLaw (Prod.fst : ℝ × ℝ → ℝ) (gaussianReal 0 1) P := measurePreserving_fst.hasLaw
  have hyf : HasLaw (Prod.snd : ℝ × ℝ → ℝ) (gaussianReal 0 1) P := measurePreserving_snd.hasLaw
  have hx := hxf.hasGaussianLaw
  have hy := hyf.hasGaussianLaw
  have hind : IndepFun (Prod.fst : ℝ × ℝ → ℝ) Prod.snd P :=
    indepFun_prod (X := id) (Y := id) measurable_id measurable_id
  have hjoint0 := hind.hasGaussianLaw hx hy
  let L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    ((Real.sqrt 2)⁻¹ • (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
      ((Real.sqrt 2)⁻¹ • (ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ))
  have hjoint : HasGaussianLaw gaussianRotate P := hjoint0.map_fun L
  have hcov0 : cov[Prod.fst, Prod.snd; P] = 0 := hind.covariance_eq_zero hx.memLp_two hy.memLp_two
  have hcov1 : cov[Prod.snd, Prod.fst; P] = 0 := by rwa [covariance_comm]
  have hxm : (∫ z, z.1 ∂P) = (0 : ℝ) := hxf.integral_eq.trans (by simp)
  have hym : (∫ z, z.2 ∂P) = (0 : ℝ) := hyf.integral_eq.trans (by simp)
  have hxv : Var[Prod.fst; P] = 1 := hxf.variance_eq.trans (by simp)
  have hyv : Var[Prod.snd; P] = 1 := hyf.variance_eq.trans (by simp)
  have hscale : ((Real.sqrt 2)⁻¹) ^ 2 = (1 / 2 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hcov : cov[fun z => (gaussianRotate z).1, fun z => (gaussianRotate z).2; P] = 0 := by
    simp only [gaussianRotate, covariance_const_mul_left, covariance_const_mul_right]
    have hz : cov[(Prod.fst : ℝ × ℝ → ℝ) + Prod.snd, Prod.fst - Prod.snd; P] = 0 := by
      rw [covariance_sub_right (hx.memLp_two.add hy.memLp_two) hx.memLp_two hy.memLp_two,
        covariance_add_left hx.memLp_two hy.memLp_two hx.memLp_two,
        covariance_add_left hx.memLp_two hy.memLp_two hy.memLp_two,
        covariance_self hx.aemeasurable, covariance_self hy.aemeasurable, hcov0, hcov1, hxv, hyv]
      norm_num
    change (Real.sqrt 2)⁻¹ * ((Real.sqrt 2)⁻¹ * cov[Prod.fst + Prod.snd, Prod.fst - Prod.snd; P]) = 0
    rw [hz]
    ring
  have hrotind : IndepFun (fun z => (gaussianRotate z).1) (fun z => (gaussianRotate z).2) P :=
    hjoint.indepFun_of_covariance_eq_zero hcov
  have ham : (∫ z, (gaussianRotate z).1 ∂P) = (0 : ℝ) := by
    change (∫ z : ℝ × ℝ, (Real.sqrt 2)⁻¹ * (z.1 + z.2) ∂P) = 0
    rw [integral_const_mul, integral_add hx.integrable hy.integrable, hxm, hym]
    ring
  have hcm : (∫ z, (gaussianRotate z).2 ∂P) = (0 : ℝ) := by
    change (∫ z : ℝ × ℝ, (Real.sqrt 2)⁻¹ * (z.1 - z.2) ∂P) = 0
    rw [integral_const_mul, integral_sub hx.integrable hy.integrable, hxm, hym]
    ring
  have hav : Var[fun z => (gaussianRotate z).1; P] = 1 := by
    rw [show (fun z => (gaussianRotate z).1) =
      (fun z : ℝ × ℝ => (Real.sqrt 2)⁻¹ * (z.1 + z.2)) from rfl,
      variance_const_mul, variance_fun_add hx.memLp_two hy.memLp_two, hcov0, hxv, hyv, hscale]
    norm_num
  have hcv : Var[fun z => (gaussianRotate z).2; P] = 1 := by
    rw [show (fun z => (gaussianRotate z).2) =
      (fun z : ℝ × ℝ => (Real.sqrt 2)⁻¹ * (z.1 - z.2)) from rfl,
      variance_const_mul, variance_fun_sub hx.memLp_two hy.memLp_two, hcov0, hxv, hyv, hscale]
    norm_num
  have hamap := hjoint.fst.map_eq_gaussianReal
  have hcmap := hjoint.snd.map_eq_gaussianReal
  change P.map (fun z => (gaussianRotate z).1) = gaussianReal (∫ z, (gaussianRotate z).1 ∂P) (Var[fun z => (gaussianRotate z).1; P]).toNNReal at hamap
  change P.map (fun z => (gaussianRotate z).2) = gaussianReal (∫ z, (gaussianRotate z).2 ∂P) (Var[fun z => (gaussianRotate z).2; P]).toNNReal at hcmap
  rw [ham, hav] at hamap
  rw [hcm, hcv] at hcmap
  refine ⟨gaussianRotate_measurable, ?_⟩
  change P.map (fun z => ((gaussianRotate z).1, (gaussianRotate z).2)) = _
  rw [IndepFun.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop) hrotind, hamap, hcmap]
  norm_num

section GaussianSum
variable {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] [DecidableEq ι]
  {P : Measure Ω} [IsProbabilityMeasure P]

variable [Fintype ι]

end GaussianSum
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uΩ uι

theorem solution : MeasurePreserving gaussianRotate
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  first
    | exact OAI.IndependentProducts.measurePreserving_gaussianRotate
    | (apply OAI.IndependentProducts.measurePreserving_gaussianRotate <;> assumption)
    | (intros; apply OAI.IndependentProducts.measurePreserving_gaussianRotate <;> assumption)
