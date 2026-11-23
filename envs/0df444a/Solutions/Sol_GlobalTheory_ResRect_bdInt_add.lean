-- Prove2me | solution 1 for GlobalTheory.ResRect.bdInt_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:48.815389+00:00
-- url     : https://prove2.me/submissions/4ed55335-9500-4824-b9db-914e162bfd4b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
import Theorems.Thm_GlobalTheory_ResRect_int_hor
import Theorems.Thm_GlobalTheory_ResRect_int_ver

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
theorem _root_.solution {a b c d : ℝ} {B : Set ℂ} (h : SidesIn a b c d B) {f g : ℂ → ℂ}
    (hf : ContinuousOn f B) (hg : ContinuousOn g B) :
    bdInt a b c d (fun s => f s + g s) = bdInt a b c d f + bdInt a b c d g := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [bdInt]
  rw [intervalIntegral.integral_add (int_hor hf h1) (int_hor hg h1),
    intervalIntegral.integral_add (int_hor hf h2) (int_hor hg h2),
    intervalIntegral.integral_add (int_ver hf h3) (int_ver hg h3),
    intervalIntegral.integral_add (int_ver hf h4) (int_ver hg h4)]
  ring
end GlobalTheory.ResRect
