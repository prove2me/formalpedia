-- Prove2me | solution 1 for GlobalTheory.Hk.RayForm.range_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:32:26.860955+00:00
-- url     : https://prove2.me/submissions/03edf84d-be19-49ca-a87e-4a6bbec29681

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PlaneLatticeShortBasisOfBoundPowTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RingOfIntegersSqrtNegThreeModFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassIdealCountEqNcardShiftedBinaryForm

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
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayForm
open GlobalTheory.Mem.PartialZeta
namespace GlobalTheory.Hk.RayForm
theorem _root_.solution (f₁ f₂ : ℂ) :
    Set.range (fun v : ℤ × ℤ => (v.1 : ℂ) * f₁ + v.2 * f₂) = (Submodule.span ℤ {f₁, f₂} : Submodule ℤ ℂ) := by
  ext z
  simp only [Set.mem_range, SetLike.mem_coe, Submodule.mem_span_pair, zsmul_eq_mul, Prod.exists]
end GlobalTheory.Hk.RayForm
