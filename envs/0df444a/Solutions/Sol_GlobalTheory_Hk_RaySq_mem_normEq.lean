-- Prove2me | solution 1 for GlobalTheory.Hk.RaySq.mem_normEq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:54.086807+00:00
-- url     : https://prove2.me/submissions/d9005d71-c40c-4320-8243-28fdc90f3109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ConvRealChar

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
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RaySq
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Hk.RaySq
theorem _root_.solution {n : ℕ} {I : Ideal (𝓞 K)} : I ∈ normEq K n ↔ Ideal.absNorm I = n := by
  simp [normEq]
end GlobalTheory.Hk.RaySq
