-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.weight_three_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:11:34.967744+00:00
-- url     : https://prove2.me/submissions/2f4d9d59-ccfb-4910-bf0d-8f6594cf6dd6

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
theorem h43_dint {s : ℝ} (hs : 0 < s) (a : ℝ) : Integrable (fun x : ℝ => density s (a - x)) := by
  have h1 : Integrable (fun y : ℝ => Real.exp (-(1/(2*s)) * y^2)) := integrable_exp_neg_mul_sq (by positivity)
  have h2 := (h1.comp_sub_left a).const_mul (Real.sqrt (2 * Real.pi * s))⁻¹
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [density]; congr 2; field_simp

theorem h43_wbdd {h : ℝ} (hh : 0 < h) {s : ℝ} (hs : 0 < s) (c x : ℝ) :
    ‖weight h c x s‖ ≤ h * (Real.sqrt (2 * Real.pi * s))⁻¹ := by
  unfold weight
  rw [Real.norm_of_nonneg (mul_nonneg hh.le (density_nonneg hs.le _))]
  apply mul_le_mul_of_nonneg_left _ hh.le
  unfold density
  have : Real.exp (-(c - x) ^ 2 / (2 * s)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [sq_nonneg (c - x)]
    · positivity
  have h0 : 0 ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ := by positivity
  nlinarith

theorem solution {h : ℝ} (hh : 0 < h) (a b c d : ℝ)
    (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v : Three) :
    Integrable (fun z : ℝ×ℝ => weight h a (chart 2 d z 0) (σ 0)*
      weight h b (chart 2 d z 1) (σ 1)*weight h c (chart 2 d z v) (σ v)) := by
  have hP : Integrable (fun z : ℝ×ℝ => weight h a (chart 2 d z 0) (σ 0)*weight h b (chart 2 d z 1) (σ 1)) := by
    have := ((h43_dint (hσ 0) a).const_mul h).mul_prod ((h43_dint (hσ 1) b).const_mul h)
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp [chart, weight]
  have hm : AEStronglyMeasurable (fun z : ℝ×ℝ => weight h c (chart 2 d z v) (σ v)) := by
    refine Continuous.aestronglyMeasurable ?_
    unfold weight density chart
    fin_cases v <;> simp <;> fun_prop
  exact hP.mul_bdd hm (Filter.Eventually.of_forall fun z => h43_wbdd hh (hσ v) c _)

