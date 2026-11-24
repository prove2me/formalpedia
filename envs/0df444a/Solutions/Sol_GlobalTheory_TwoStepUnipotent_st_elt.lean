-- Prove2me | solution 1 for GlobalTheory.TwoStepUnipotent.st_elt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:42:27.77713+00:00
-- url     : https://prove2.me/submissions/4a54e6c1-6779-4ed1-b8a5-5512f9135622

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_TwoStepUnipotentCompactModSubring
import Theorems.Thm_GlobalTheory_TwoStepUnipotent_st_one
import Theorems.Thm_GlobalTheory_TwoStepUnipotent_st_half

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
    (hh : h + h = 1) (hc : ∀ x, h * x = x * h) (b : S) {w : S} (hw : st w = -w) :
    st (elt st h b w) = elt st h (-b) (-w) := by
  simp only [elt, map_add, map_sub, map_neg, st_one hm hi, hi, hm, hw, st_half hm hi hh hc, neg_mul,
    mul_neg, neg_neg]
  rw [hc (st b * b)]
  abel
end GlobalTheory.TwoStepUnipotent
