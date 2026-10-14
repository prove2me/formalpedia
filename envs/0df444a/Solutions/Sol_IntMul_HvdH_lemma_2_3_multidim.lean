-- Prove2me | solution 1 for IntMul.HvdH.lemma_2_3_multidim
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-11T20:38:38.310991+00:00
-- url     : https://prove2.me/submissions/ece2f2fb-99d8-48de-9c8b-361a08fc307a

import Mathlib

open ZMod

namespace ConvAux

variable {d : ℕ} (s : Fin d → ℕ) [∀ i, NeZero (s i)]

/-- `e(t, a) = ∏ᵢ exp(2πi tᵢ aᵢ / sᵢ)` -/
noncomputable def ee (t a : Π i, ZMod (s i)) : ℂ := ∏ i, stdAddChar (t i * a i)

lemma ee_add (t a b : Π i, ZMod (s i)) : ee s t (a + b) = ee s t a * ee s t b := by
  unfold ee; rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [mul_add, AddChar.map_add_eq_mul]

lemma sum_ee (a : Π i, ZMod (s i)) :
    ∑ t, ee s t a = if a = 0 then (Fintype.card (Π i, ZMod (s i)) : ℂ) else 0 := by
  unfold ee
  rw [← Fintype.prod_sum (fun i (x : ZMod (s i)) => stdAddChar (x * a i))]
  simp_rw [AddChar.sum_mulShift _ (isPrimitive_stdAddChar _)]
  split_ifs with h
  · subst h; simp [Fintype.card_pi]
  · obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra hc; push Not at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

end ConvAux

open ConvAux

theorem solution {d : ℕ} (s : Fin d → ℕ) [∀ i, NeZero (s i)]
    (u v : (Π i, ZMod (s i)) → ℂ) (j : Π i, ZMod (s i)) :
    ∑ k, u k * v (j - k) =
      (1 / (Fintype.card (Π i, ZMod (s i)) : ℂ)) *
        ∑ t : Π i, ZMod (s i), (∏ i, stdAddChar (t i * j i)) *
          ((∑ k : Π i, ZMod (s i), (∏ i, stdAddChar (-(t i * k i))) * u k) *
           (∑ k : Π i, ZMod (s i), (∏ i, stdAddChar (-(t i * k i))) * v k)) := by
  have hn : (Fintype.card (Π i, ZMod (s i)) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  -- rewrite everything through `ee`
  have hneg : ∀ t k : Π i, ZMod (s i), (∏ i, stdAddChar (-(t i * k i))) = ee s t (-k) := by
    intro t k; unfold ee; simp [mul_neg]
  simp_rw [hneg]
  change _ = _ * ∑ t, ee s t j * _
  simp_rw [Finset.sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  have key : ∀ k l : Π i, ZMod (s i),
      ∑ t, ee s t j * (ee s t (-k) * u k * (ee s t (-l) * v l)) =
        u k * v l * (if j - k - l = 0 then (Fintype.card (Π i, ZMod (s i)) : ℂ) else 0) := by
    intro k l
    rw [← sum_ee s (j - k - l), Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have : ee s t (j - k - l) = ee s t j * ee s t (-k) * ee s t (-l) := by
      rw [sub_eq_add_neg, sub_eq_add_neg, ee_add, ee_add]
    rw [this]; ring
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, key]
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have : (Finset.univ.filter fun l : Π i, ZMod (s i) => j - k - l = 0) = {j - k} := by
    ext l; simp [sub_eq_zero, eq_comm]
  rw [this, Finset.sum_singleton]
  field_simp
