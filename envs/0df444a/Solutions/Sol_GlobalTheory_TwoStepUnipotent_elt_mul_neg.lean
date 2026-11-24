-- Prove2me | solution 1 for GlobalTheory.TwoStepUnipotent.elt_mul_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:07:19.132715+00:00
-- url     : https://prove2.me/submissions/815a9f63-b6b4-4da9-bda4-cc48302a4a97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_TwoStepUnipotentCompactModSubring
import Theorems.Thm_GlobalTheory_TwoStepUnipotent_elt_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory GlobalTheory.TwoStepUnipotent
variable {S : Type} [Ring S] (st : S →+ S) (e₁ e₃ h : S)
variable {st e₁ e₃ h}
namespace GlobalTheory.TwoStepUnipotent
theorem _root_.solution (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (hs : st e₁ = e₃) (h31 : e₃ * e₁ = 0) (hh : h + h = 1) (hc : ∀ x, h * x = x * h)
    {b w : S} (hb : e₃ * b = 0 ∧ b * e₃ = b) (hw : e₁ * w = w ∧ w * e₃ = w) :
    elt st h b w * elt st h (-b) (-w) = 1 := by
  rw [elt_mul hm hi hs h31 hh hc hb ⟨by rw [mul_neg, hb.1, neg_zero], by rw [neg_mul, hb.2]⟩ hw.2
    (by rw [mul_neg, hw.1])]
  simp [elt]
end GlobalTheory.TwoStepUnipotent
