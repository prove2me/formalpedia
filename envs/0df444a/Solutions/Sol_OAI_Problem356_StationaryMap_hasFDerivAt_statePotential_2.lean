-- Prove2me | solution 2 for OAI.Problem356.StationaryMap.hasFDerivAt_statePotential
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:25:47.563497+00:00
-- url     : https://prove2.me/submissions/3460a771-4903-4db9-bd5f-8c3ca2079329

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/StationaryMap.lean:L84-L103
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.StationaryMap.hasFDerivAt_statePotential. The node keeps its source
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
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap

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

end Problem356.CoulombCalculus

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.StationaryMap ----
namespace OAI

universe uE

noncomputable section

open scoped RealInnerProductSpace

namespace Problem356.StationaryMap

open CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The displayed stationary equation really is the state derivative of the supporting potential. -/
theorem hasFDerivAt_statePotential (a y : E) {s : E × E}
    (hxy : s.1 ≠ y) (hxz : s.1 ≠ s.2) (hzy : s.2 ≠ y) :
    HasFDerivAt (statePotential a y) (stateDifferential a y s) s := by
  have hX : HasFDerivAt (fun q : E × E => q.1)
      (ContinuousLinearMap.fst ℝ E E) s := hasFDerivAt_fst
  have hZ : HasFDerivAt (fun q : E × E => q.2)
      (ContinuousLinearMap.snd ℝ E E) s := hasFDerivAt_snd
  have hXY := (hasFDerivAt_pairCost (sub_ne_zero.mpr hxy)).comp s (hX.sub_const y)
  have hXZ := (hasFDerivAt_pairCost (sub_ne_zero.mpr hxz)).comp s (hX.sub hZ)
  have hZY := (hasFDerivAt_pairCost (sub_ne_zero.mpr hzy)).comp s (hZ.sub_const y)
  have h := (((hXY.add hXZ).add hZY).sub
    ((hasFDerivAt_const ((5 : ℝ) / 2) s).sub (hX.norm_sq.const_mul 10))).sub
    ((((hasFDerivAt_const a s).inner ℝ (hZ.add_const a)).const_mul ((5 : ℝ) / 4)).sub
      ((hZ.add_const a).norm_sq.const_mul 10))
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [stateDifferential, stationary, pairGradient, mul_sub, norm_sub_rev s.2 s.1]
  ring

end Problem356.StationaryMap

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.StationaryMap
open scoped RealInnerProductSpace
open CoulombCalculus


theorem solution.{uE} : type_of% @_root_.OAI.Problem356.StationaryMap.hasFDerivAt_statePotential.{uE} := @_root_.OAI.Problem356.StationaryMap.hasFDerivAt_statePotential.{uE}
