-- Prove2me | solution 1 for GlobalTheory.ThetaWeberRoad.OddDeriv.hasDerivAt_mul_of_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:33:32.63261+00:00
-- url     : https://prove2.me/submissions/02017b1c-d449-40cc-9610-370d26df86a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HasDerivAtOddJacobiThetaZeroEtaCube

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open UpperHalfPlane hiding I
open scoped Real
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.ThetaWeberRoad GlobalTheory.ThetaWeberRoad.OddDeriv
namespace GlobalTheory.ThetaWeberRoad.OddDeriv
theorem _root_.solution {F R : ℂ → ℂ} {F' : ℂ} (hF : HasDerivAt F F' 0) (hF0 : F 0 = 0)
    (hR : ContinuousAt R 0) : HasDerivAt (fun z => F z * R z) (F' * R 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope] at hF ⊢
  have hR' : Tendsto R (𝓝[≠] (0 : ℂ)) (𝓝 (R 0)) := hR.tendsto.mono_left nhdsWithin_le_nhds
  refine (hF.mul hR').congr' ?_
  filter_upwards with z
  simp only [slope_def_field, hF0, sub_zero, zero_mul]
  ring
end GlobalTheory.ThetaWeberRoad.OddDeriv
