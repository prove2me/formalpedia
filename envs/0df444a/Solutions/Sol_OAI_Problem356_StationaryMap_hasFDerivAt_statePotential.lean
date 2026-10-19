-- Prove2me | solution 1 for OAI.Problem356.StationaryMap.hasFDerivAt_statePotential
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:05:34.20143+00:00
-- url     : https://prove2.me/submissions/49a19131-712a-45f5-ab2c-9e6551c754c0

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

open OAI OAI.Problem356 OAI.Problem356.StationaryMap
universe uE
open scoped RealInnerProductSpace
open CoulombCalculus
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open OAI OAI.Problem356 CoulombCalculus in
theorem ap_pc {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {x : E} (hx : x ≠ 0) :
    HasFDerivAt (pairCost : E → ℝ) (innerSL ℝ (pairGradient x)) x := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : (0:ℝ) < ‖x‖ ^ 2 := by positivity
  have h1 : HasFDerivAt (fun y : E => ‖y‖ ^ 2) (2 • innerSL ℝ x) x := by
    simpa using (hasFDerivAt_id x).norm_sq
  have hs : HasDerivAt Real.sqrt (1 / (2 * √(‖x‖^2))) (‖x‖^2) := Real.hasDerivAt_sqrt hu.ne'
  have hi : HasDerivAt (fun u : ℝ => u⁻¹) (-(√(‖x‖^2) ^ 2)⁻¹) (√(‖x‖^2)) :=
    hasDerivAt_inv (by positivity)
  have hc := (hi.comp _ hs).comp_hasFDerivAt x h1
  have heq : (pairCost : E → ℝ) = ((fun u : ℝ => u⁻¹) ∘ Real.sqrt) ∘ (fun y : E => ‖y‖ ^ 2) := by
    funext y; simp [pairCost, Real.sqrt_sq (norm_nonneg y)]
  rw [heq]
  refine hc.congr_fderiv ?_
  ext v
  rw [Real.sqrt_sq hn.le]
  simp only [pairGradient, innerSL_apply_apply, inner_smul_left, ContinuousLinearMap.smul_apply, smul_eq_mul, RCLike.conj_to_real]
  field_simp
  ring

theorem solution (a y : E) {s : E × E}
    (hxy : s.1 ≠ y) (hxz : s.1 ≠ s.2) (hzy : s.2 ≠ y) :
    HasFDerivAt (statePotential a y) (stateDifferential a y s) s := by
  have h1 := (ap_pc (sub_ne_zero.mpr hxy)).comp s ((hasFDerivAt_fst (p := s)).sub_const y)
  have h2 := (ap_pc (sub_ne_zero.mpr hxz)).comp s ((hasFDerivAt_fst (p := s)).sub (hasFDerivAt_snd (p := s)))
  have h3 := (ap_pc (sub_ne_zero.mpr hzy)).comp s ((hasFDerivAt_snd (p := s)).sub_const y)
  have h4 := (hasFDerivAt_fst (p := s)).norm_sq
  have h5 := (hasFDerivAt_snd (p := s)).add_const a |>.norm_sq
  have h6 := (innerSL ℝ a).hasFDerivAt.comp s ((hasFDerivAt_snd (p := s)).add_const a)
  have H := (((h1.add h2).add h3).sub ((hasFDerivAt_const ((5:ℝ)/2) s).sub (h4.const_mul 10))).sub
    ((h6.const_mul ((5:ℝ)/4)).sub (h5.const_mul 10))
  have H' : HasFDerivAt (statePotential a y) _ s := H
  refine H'.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun ⟨u, w⟩ => ?_
  have hn : pairGradient (s.2 - s.1) = - pairGradient (s.1 - s.2) := by
    rw [← neg_sub, pairGradient_neg]
  simp [stateDifferential, stationary, hn, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, inner_sub_left, inner_sub_right, inner_neg_left, real_inner_comm]
  ring

