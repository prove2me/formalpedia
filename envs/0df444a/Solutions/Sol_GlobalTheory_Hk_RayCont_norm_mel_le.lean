-- Prove2me | solution 1 for GlobalTheory.Hk.RayCont.norm_mel_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:07:02.596258+00:00
-- url     : https://prove2.me/submissions/80ec7649-b70e-410b-96e3-52823889c6ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth
import Theorems.Thm_GlobalTheory_Hk_RayCont_norm_integral_le
import Theorems.Thm_GlobalTheory_Hk_RayCont_norm_rem_le

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
theorem _root_.solution {s : ℂ} (hs : 1 / 2 < s.re) : ‖𝓕.mel χ s‖ ≤ 10 * 𝓕.B / (s.re - 1 / 2) :=
  norm_integral_le (norm_rem_le 𝓕 χ) hs
end GlobalTheory.Hk.RayCont
