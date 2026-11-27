-- Prove2me | solution 1 for GlobalTheory.taylorDir_eq_taylor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:42:02.431451+00:00
-- url     : https://prove2.me/submissions/2cb92bce-7b3f-4339-8cbb-fa6e2e2710d4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Theorems.Thm_GlobalTheory_taylor_comp_clm
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero



set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {f g : (σ → ℂ) → ℂ}
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace GlobalTheory
theorem _root_.solution (u : σ → W) {F : W → ℂ} (hF : AnalyticAt ℂ F 0) :
    taylorDir u F = taylor fun z : σ → ℂ => F (∑ i, z i • u i) := by
  have h := taylor_comp_clm (LinearMap.toContinuousLinearMap (Fintype.linearCombination ℂ u)) hF
  simp only [LinearMap.coe_toContinuousLinearMap', Fintype.linearCombination_apply_single,
    one_smul] at h
  rw [← h]
  rfl
end GlobalTheory
