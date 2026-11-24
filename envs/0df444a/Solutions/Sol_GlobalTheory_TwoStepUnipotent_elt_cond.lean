-- Prove2me | solution 1 for GlobalTheory.TwoStepUnipotent.elt_cond
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:17:56.683409+00:00
-- url     : https://prove2.me/submissions/61fbc398-f653-4c07-a2f6-9a8606fa4690

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_TwoStepUnipotentCompactModSubring
import Theorems.Thm_GlobalTheory_TwoStepUnipotent_st_elt
import Theorems.Thm_GlobalTheory_TwoStepUnipotent_elt_neg_mul

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
    {b w : S} (hb : e₁ * b = 0 ∧ e₃ * b = 0 ∧ b * e₃ = b)
    (hw : e₁ * w = w ∧ w * e₃ = w ∧ st w = -w) :
    st (elt st h b w) * elt st h b w = 1 ∧ (elt st h b w - 1) * e₁ = 0 ∧
      (1 - e₁) * (elt st h b w - 1) * (1 - e₃) = 0 := by
  obtain ⟨hb1, hb3, hb3'⟩ := hb
  obtain ⟨hw1, hw3, hws⟩ := hw
  have he3 : st e₃ = e₁ := by rw [← hs, hi]
  have f1 : st b * e₃ = 0 := by rw [← hs, ← hm, hb1, map_zero]
  have f2 : e₁ * st b = st b := by rw [← he3, ← hm, hb3']
  have f3 : b * e₁ = 0 := by rw [← hb3', mul_assoc, h31, mul_zero]
  have f4 : w * e₁ = 0 := by rw [← hw3, mul_assoc, h31, mul_zero]
  have f5 : st b * e₁ = 0 := by rw [← he3, ← hm, hb3, map_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [st_elt hm hi hh hc b hws]
    exact elt_neg_mul hm hi hs h31 hh hc ⟨hb3, hb3'⟩ ⟨hw1, hw3⟩
  · have e : (elt st h b w - 1) * e₁ = -(st b * e₁) + b * e₁ + (w * e₁ - h * (st b * (b * e₁))) := by
      simp only [elt, sub_mul, add_mul, one_mul, mul_assoc]
      abel
    rw [e, f5, f3, f4]
    simp
  · have hX : (elt st h b w - 1) * (1 - e₃) = -st b := by
      have e : (elt st h b w - 1) * (1 - e₃) =
          -st b + b + (w - h * (st b * b)) - (-(st b * e₃) + b * e₃ + (w * e₃ - h * (st b * (b * e₃)))) := by
        simp only [elt, sub_mul, mul_sub, add_mul, one_mul, mul_one, mul_assoc]
        abel
      rw [e, f1, hb3', hw3]
      abel
    rw [mul_assoc, hX, mul_neg, sub_mul, one_mul, f2, sub_self, neg_zero]
end GlobalTheory.TwoStepUnipotent
