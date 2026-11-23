-- Prove2me | solution 1 for GlobalTheory.ResRect.int_hor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:27.213008+00:00
-- url     : https://prove2.me/submissions/e66466e5-b23d-4951-a84d-7083f16e1a91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.ResRect
namespace GlobalTheory.ResRect
theorem _root_.solution {f : ℂ → ℂ} {B : Set ℂ} (hf : ContinuousOn f B) {a b c : ℝ}
    (h : ∀ x ∈ Set.uIcc a b, (x : ℂ) + c * I ∈ B) :
    IntervalIntegrable (fun x : ℝ => f (x + c * I)) volume a b :=
  (hf.comp (by fun_prop) h).intervalIntegrable
end GlobalTheory.ResRect
