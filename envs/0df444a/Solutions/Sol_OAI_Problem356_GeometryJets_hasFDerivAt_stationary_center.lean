-- Prove2me | solution 1 for OAI.Problem356.GeometryJets.hasFDerivAt_stationary_center
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:03:58.614348+00:00
-- url     : https://prove2.me/submissions/6aa6b162-dddb-46b1-9e10-7f0a6e6a0585

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/StationaryEquation.lean:L135-L163
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.GeometryJets.hasFDerivAt_stationary_center. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation

-- ---- from OAI.Analysis.CoulombTransport.CoulombCalculus ----
namespace OAI

universe uE

noncomputable section

open scoped RealInnerProductSpace

namespace Problem356.CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hasFDerivAt_norm_explicit {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  simp only [Real.sqrt_sq (norm_nonneg x)] at h
  convert h using 1
  · ext y
    simp [Real.sqrt_sq (norm_nonneg y)]
  · ext y
    simp only [smul_apply, smul_eq_mul]
    field_simp
    simp [mul_comm]

lemma hasFDerivAt_pairCost {x : E} (hx : x ≠ 0) :
    HasFDerivAt (pairCost : E → ℝ) (-(‖x‖ ^ 3)⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := (hasDerivAt_inv hn).comp_hasFDerivAt x (hasFDerivAt_norm_explicit hx)
  have hs : -(‖x‖ ^ 2)⁻¹ * ‖x‖⁻¹ = -(‖x‖ ^ 3)⁻¹ := by
    field_simp
  convert! h using 1
  simp only [smul_smul, hs]

lemma hasFDerivAt_radialFactor {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => -(‖y‖ ^ 3)⁻¹)
      ((3 * (‖x‖ ^ 5)⁻¹) • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := ((hasFDerivAt_pairCost hx).pow 3).neg
  convert! h using 1
  · ext y
    simp [pairCost, inv_pow]
  · ext y
    simp only [smul_apply, smul_eq_mul, neg_apply, pairCost]
    norm_num
    field_simp

lemma hasFDerivAt_pairGradient {x : E} (hx : x ≠ 0) :
    HasFDerivAt (pairGradient : E → E) (pairHessian x) x := by
  have h := (hasFDerivAt_radialFactor hx).smul (hasFDerivAt_id x)
  convert! h using 1
  ext y
  simp [pairHessian, ContinuousLinearMap.smulRight_apply, smul_smul]

end Problem356.CoulombCalculus

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.GeometryJets ----
namespace OAI

universe uE

noncomputable section

open scoped RealInnerProductSpace

namespace Problem356.GeometryJets

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem center_nonzero {a : E} (ha : ‖a‖ = 1) : a ≠ 0 := by
  intro h
  simp [h] at ha

end Problem356.GeometryJets

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.StationaryEquation ----
namespace OAI

universe uE

noncomputable section

namespace Problem356.GeometryJets

open CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma hessian_double_center (a : E) (ha : ‖a‖ = 1) :
    pairHessian ((2 : ℝ) • a) = (1 / 8 : ℝ) • pairHessian a := by
  apply ContinuousLinearMap.ext
  intro v
  simp [pairHessian, innerSL, ContinuousLinearMap.smulRight_apply, norm_smul, ha]
  module

lemma hasFDerivAt_stationary_center (K : ℝ) (a : E) (ha : ‖a‖ = 1) :
    HasFDerivAt (stationaryEquation K a)
      (centerTotalDerivative K (pairHessian a)) (a, (0, -a)) := by
  have ha0 := center_nonzero ha
  have hneg : -a ≠ 0 := neg_ne_zero.mpr ha0
  have hvec : a - -a = (2 : ℝ) • a := by module
  have hdouble : a - -a ≠ 0 := by
    rw [hvec]
    exact smul_ne_zero (by norm_num) ha0
  have hy : HasFDerivAt (fun p : E × (E × E) => p.1)
      (ContinuousLinearMap.fst ℝ E (E × E)) (a, (0, -a)) := hasFDerivAt_fst
  have hs : HasFDerivAt (fun p : E × (E × E) => p.2)
      (ContinuousLinearMap.snd ℝ E (E × E)) (a, (0, -a)) := hasFDerivAt_snd
  have hx := hs.fst
  have hz := hs.snd
  have h1 := (hasFDerivAt_pairGradient (show (0 : E) - a ≠ 0 by simpa using hneg)).comp
    (a, (0, -a)) (hx.sub hy)
  have h2 := (hasFDerivAt_pairGradient (show (0 : E) - -a ≠ 0 by simpa using ha0)).comp
    (a, (0, -a)) (hx.sub hz)
  have h3 := (hasFDerivAt_pairGradient hdouble).comp (a, (0, -a)) (hy.sub hz)
  have hfirst := (h1.add h2).add (hx.const_smul K)
  have hsecond := ((h2.neg.sub h3).sub_const ((5 / 4 : ℝ) • a)).add
    ((hz.add_const a).const_smul K)
  convert! hfirst.prodMk hsecond using 1
  apply ContinuousLinearMap.ext
  intro p
  simp [centerTotalDerivative, centerParameterDerivative, centerStateHessian,
    hvec, hessian_double_center a ha]
  constructor <;> module

end Problem356.GeometryJets

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.GeometryJets
open CoulombCalculus


theorem solution.{uE} : type_of% @_root_.OAI.Problem356.GeometryJets.hasFDerivAt_stationary_center.{uE} := @_root_.OAI.Problem356.GeometryJets.hasFDerivAt_stationary_center.{uE}
