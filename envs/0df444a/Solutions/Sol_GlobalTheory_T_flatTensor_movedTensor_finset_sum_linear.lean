-- Prove2me | solution 1 for GlobalTheory.T.flatTensor_movedTensor_finset_sum_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:18:01.887173+00:00
-- url     : https://prove2.me/submissions/51737ecc-243d-4c9e-b59a-f3fb0a23e111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorMovedTensorFinsetSumLinear
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorMovedTensorFinsetSumLinearStatement
import Theorems.Thm_GlobalTheory_FunObj_flatTensor_moved_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.FunObj
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : GlobalTheory.SplitFlip.Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure], Continuous ψ → ∀ (ϖ : kˣ) (e : ℕ) (keep : Bool) (g : G.VertexGroup) {ι : Type} (S : Finset ι) (x : ι → ℂ) (T : ι → G.Args → ℂ), (∀ i ∈ S, G.IsTensor ϖ e (GlobalTheory.SplitFlip.oppositePath G.m) (T i)) → ∀ X Y, flatTensor hs ψ ν (moved G keep g (fun z => ∑ i ∈ S, x i * T i z)) X Y = ∑ i ∈ S, x i * flatTensor hs ψ ν (moved G keep g (T i)) X Y := by
  first | exact @GlobalTheory.FunObj.flatTensor_moved_sum | exact GlobalTheory.FunObj.flatTensor_moved_sum | (intros; apply GlobalTheory.FunObj.flatTensor_moved_sum <;> assumption)
end _root_.GlobalTheory.T
