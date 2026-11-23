-- Prove2me | solution 1 for GlobalTheory.ResRect.int_ver
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:27.207832+00:00
-- url     : https://prove2.me/submissions/b5dbdd58-5e42-4fad-b7c0-dbc1a1f579a9

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
theorem _root_.solution {f : ℂ → ℂ} {B : Set ℂ} (hf : ContinuousOn f B) {a c d : ℝ}
    (h : ∀ y ∈ Set.uIcc c d, (a : ℂ) + y * I ∈ B) :
    IntervalIntegrable (fun y : ℝ => f (a + y * I)) volume c d :=
  (hf.comp (by fun_prop) h).intervalIntegrable
end GlobalTheory.ResRect
