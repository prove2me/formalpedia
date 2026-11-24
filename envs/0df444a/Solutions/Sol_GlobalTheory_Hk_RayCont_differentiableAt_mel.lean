-- Prove2me | solution 1 for GlobalTheory.Hk.RayCont.differentiableAt_mel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:07:01.748607+00:00
-- url     : https://prove2.me/submissions/40a0ed24-1764-45f2-9dae-0b3129bd61f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth
import Theorems.Thm_GlobalTheory_Hk_RayCont_differentiableAt_integral
import Theorems.Thm_GlobalTheory_Hk_RayCont_norm_rem_le
import Theorems.Thm_GlobalTheory_Hk_RayCont_measurable_rem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayCont
open Asymptotics
variable (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ)
namespace GlobalTheory.Hk.RayCont
theorem _root_.solution {s : ℂ} (hs : 1 / 2 < s.re) : DifferentiableAt ℂ (𝓕.mel χ) s :=
  differentiableAt_integral (measurable_rem 𝓕 χ) (norm_rem_le 𝓕 χ) hs
end GlobalTheory.Hk.RayCont
