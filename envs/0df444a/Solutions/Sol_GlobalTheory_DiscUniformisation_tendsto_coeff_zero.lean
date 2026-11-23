-- Prove2me | solution 1 for GlobalTheory.DiscUniformisation.tendsto_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:16.050005+00:00
-- url     : https://prove2.me/submissions/09a3f590-f3c7-47d8-b39d-238fb7744fb6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TendstoCoeffZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm MatrixGroups EisensteinSeries Filter Topology
open GlobalTheory GlobalTheory.DiscUniformisation
namespace GlobalTheory.DiscUniformisation
theorem _root_.solution {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    Tendsto f atImInfty (𝓝 ((qExpansion 1 f).coeff 0)) := by
  have hp := one_mem_strictPeriods_SL
  have han := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hp
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f hp
  rw [UpperHalfPlane.qExpansion_coeff_zero one_pos han hper,
    ← UpperHalfPlane.cuspFunction_apply_zero one_pos han hper]
  refine (han.continuousAt.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty one_pos)).congr
    fun τ => ?_
  exact UpperHalfPlane.eq_cuspFunction τ one_ne_zero hper
end GlobalTheory.DiscUniformisation
