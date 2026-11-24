-- Prove2me | solution 1 for GlobalTheory.ThetaRational.eq_zero_of_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:33:02.682098+00:00
-- url     : https://prove2.me/submissions/3810c7e4-aefb-4ee5-9783-34e17f9cd075

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta
import Theorems.Thm_GlobalTheory_SCV_eqOn_of_eventuallyEq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
omit [FiniteDimensional ℂ W] [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace GlobalTheory.ThetaRational
theorem _root_.solution {u v : E → ℂ} (hu : Continuous u) (hv : Differentiable ℂ v)
    (hu0 : u ≠ 0) (h : ∀ e, u e ≠ 0 → v e = 0) : v = 0 := by
  obtain ⟨e, he⟩ := Function.ne_iff.1 hu0
  have h1 : v =ᶠ[𝓝 e] 0 := (hu.continuousAt.eventually_ne he).mono h
  have := GlobalTheory.SCV.eqOn_of_eventuallyEq isOpen_univ isPreconnected_univ hv.differentiableOn
    (differentiableOn_const (0 : ℂ)) (Set.mem_univ e) h1
  exact funext fun x => this (Set.mem_univ x)
end GlobalTheory.ThetaRational
