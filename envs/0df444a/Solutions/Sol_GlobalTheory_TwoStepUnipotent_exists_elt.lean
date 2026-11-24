-- Prove2me | solution 1 for GlobalTheory.TwoStepUnipotent.exists_elt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:14:34.776092+00:00
-- url     : https://prove2.me/submissions/6179f416-8aee-47bf-8643-5751bd87bc91

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
    (h11 : e₁ * e₁ = e₁)
    (hs : st e₁ = e₃) (h31 : e₃ * e₁ = 0) (hh : h + h = 1) (hc : ∀ x, h * x = x * h)
    {g : S} (h1 : st g * g = 1) (h2 : (g - 1) * e₁ = 0)
    (h3 : (1 - e₁) * (g - 1) * (1 - e₃) = 0) :
    ∃ b w, (e₁ * b = 0 ∧ e₃ * b = 0 ∧ b * e₃ = b) ∧ (e₁ * w = w ∧ w * e₃ = w ∧ st w = -w) ∧
      g = elt st h b w := by
  have he3 : st e₃ = e₁ := by rw [← hs, hi]
  have he33 : e₃ * e₃ = e₃ := by rw [← hs, ← hm, h11]
  obtain ⟨X, rfl⟩ : ∃ X, g = 1 + X := ⟨g - 1, by abel⟩
  have hX1 : X * e₁ = 0 := by rwa [add_sub_cancel_left] at h2
  have h3' : (1 - e₁) * X * (1 - e₃) = 0 := by rwa [add_sub_cancel_left] at h3
  have hU : st X + X + st X * X = 0 := by
    rw [map_add, st_one hm hi] at h1
    have e : (1 + st X) * (1 + X) = 1 + (st X + X + st X * X) := by noncomm_ring
    rw [e] at h1
    exact add_left_cancel (h1.trans (add_zero 1).symm)
  have hsX1 : st X * e₁ = 0 := by
    have e := congrArg (· * e₁) hU
    simp only [add_mul, mul_assoc, hX1, mul_zero, add_zero, zero_mul] at e
    exact e
  have he3X : e₃ * X = 0 := by
    have e : st (e₃ * X) = 0 := by rw [hm, he3, hsX1]
    rw [← hi (e₃ * X), e, map_zero]
  obtain ⟨b, hbdef⟩ : ∃ b, b = (1 - e₁) * X * e₃ := ⟨_, rfl⟩
  have hXb : X = b + e₁ * X := by
    have e : (1 - e₁) * X = b := by
      rw [hbdef]
      have e' := h3'
      rw [mul_sub, mul_one, sub_eq_zero] at e'
      exact e'
    rw [← e, sub_mul, one_mul]
    abel
  have hb1 : e₁ * b = 0 := by
    rw [hbdef]
    simp only [← mul_assoc, mul_sub, mul_one, h11, sub_self, zero_mul]
  have hb3 : e₃ * b = 0 := by
    rw [hbdef]
    simp only [← mul_assoc, mul_sub, mul_one, h31, sub_zero, he3X, zero_mul]
  have hb3' : b * e₃ = b := by rw [hbdef, mul_assoc, he33]
  have sb1 : e₁ * st b = st b := by rw [← he3, ← hm, hb3']
  have sb3 : st b * e₃ = 0 := by rw [← hs, ← hm, hb1, map_zero]
  have hsX : st X = st b + st X * e₃ := by
    conv_lhs => rw [hXb]
    rw [map_add, hm, hs]
  have hXX : st X * X = st b * b := by
    calc st X * X = st X * (b + e₁ * X) := by rw [← hXb]
      _ = st X * b + st X * e₁ * X := by rw [mul_add, mul_assoc]
      _ = (st b + st X * e₃) * b := by rw [hsX1, zero_mul, add_zero, ← hsX]
      _ = st b * b := by rw [add_mul, mul_assoc, hb3, mul_zero, add_zero]
  have hstar : st b + st X * e₃ + b + e₁ * X + st b * b = 0 := by
    have e := hU
    rw [hXX] at e
    calc st b + st X * e₃ + b + e₁ * X + st b * b = (st b + st X * e₃) + (b + e₁ * X) + st b * b := by abel
      _ = st X + X + st b * b := by rw [← hsX, ← hXb]
      _ = 0 := e
  have hYe : e₁ * X * e₃ = e₁ * X + st b := by
    have e := congrArg (· * e₃) hstar
    simp only [add_mul, zero_mul] at e
    rw [sb3, mul_assoc (st X), he33, hb3', mul_assoc (st b), hb3'] at e
    have key : e₁ * X * e₃ - (e₁ * X + st b) =
        (0 + st X * e₃ + b + e₁ * X * e₃ + st b * b) - (st b + st X * e₃ + b + e₁ * X + st b * b) := by abel
    rw [e, hstar, sub_zero] at key
    exact sub_eq_zero.mp key
  have hq : h * (st b * b) + h * (st b * b) = st b * b := by rw [← add_mul, hh, one_mul]
  refine ⟨b, e₁ * X + st b + h * (st b * b), ⟨hb1, hb3, hb3'⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [mul_add, mul_add, ← mul_assoc, h11, sb1, ← mul_assoc, ← hc e₁, mul_assoc, ← mul_assoc e₁, sb1]
  · rw [add_mul, add_mul, hYe, sb3, add_zero, mul_assoc h, mul_assoc (st b), hb3']
  · have e : st (e₁ * X + st b + h * (st b * b)) + (e₁ * X + st b + h * (st b * b)) = 0 := by
      simp only [map_add, hm, hs, hi, st_half hm hi hh hc]
      rw [← hc (st b * b)]
      calc st X * e₃ + b + h * (st b * b) + (e₁ * X + st b + h * (st b * b))
          = st b + st X * e₃ + b + e₁ * X + (h * (st b * b) + h * (st b * b)) := by abel
        _ = 0 := by rw [hq]; exact hstar
    exact eq_neg_of_add_eq_zero_left e
  · simp only [elt]
    conv_lhs => rw [hXb]
    abel
end GlobalTheory.TwoStepUnipotent
