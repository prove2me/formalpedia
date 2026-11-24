-- Prove2me | solution 1 for GlobalTheory.ResRect.bdInt_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:56:32.894796+00:00
-- url     : https://prove2.me/submissions/dfabf6bc-10a7-4a69-9382-6aec25800de2

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
theorem _root_.solution {a b c d : ℝ} {B : Set ℂ} (h : SidesIn a b c d B) {f g : ℂ → ℂ}
    (hfg : ∀ s ∈ B, f s = g s) : bdInt a b c d f = bdInt a b c d g := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [bdInt]
  rw [intervalIntegral.integral_congr (g := fun x : ℝ => g (x + c * I)) fun x hx => hfg _ (h1 x hx),
    intervalIntegral.integral_congr (f := fun x : ℝ => f (x + d * I))
      (g := fun x : ℝ => g (x + d * I)) fun x hx => hfg _ (h2 x hx),
    intervalIntegral.integral_congr (f := fun y : ℝ => f (b + y * I))
      (g := fun y : ℝ => g (b + y * I)) fun x hx => hfg _ (h3 x hx),
    intervalIntegral.integral_congr (f := fun y : ℝ => f (a + y * I))
      (g := fun y : ℝ => g (a + y * I)) fun x hx => hfg _ (h4 x hx)]
end GlobalTheory.ResRect
