-- Prove2me | solution 1 for GlobalTheory.ResRect.bdInt_eq_zero_of_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:56:33.697835+00:00
-- url     : https://prove2.me/submissions/ea09ccd2-5a7b-464e-886d-188ed8fe8ff0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
import Theorems.Thm_GlobalTheory_ResRect_ftc_hor
import Theorems.Thm_GlobalTheory_ResRect_ftc_ver

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
theorem _root_.solution {a b c d : ℝ} {B : Set ℂ} (h : SidesIn a b c d B)
    {F f : ℂ → ℂ} (hf : ContinuousOn f B) (hF : ∀ s ∈ B, HasDerivAt F (f s) s) :
    bdInt a b c d f = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [bdInt]
  rw [ftc_hor hf hF h1, ftc_hor hf hF h2, ftc_ver hf hF h3, ftc_ver hf hF h4]
  ring
end GlobalTheory.ResRect
