-- Prove2me | solution 1 for HuangYin.transparent_benchmark
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:27:02.431754+00:00
-- url     : https://prove2.me/submissions/1349a42c-2542-42e5-bf41-616264443e72

import Mathlib
import Definitions.Def_HuangYin_transparentProfit

open HuangYin in
theorem solution (P : Params) :
    (0 ≤ max (P.vH - P.cH) (P.vL - P.cL) → ∀ (m1 m2 : Product) (p1 p2 : ℝ),
      transparentProfit P m1 m2 p1 p2 ≤ 2 * max (P.vH - P.cH) (P.vL - P.cL)) ∧
    (P.vL - P.cL ≤ P.vH - P.cH →
      transparentProfit P .H .H P.vH P.vH = 2 * (P.vH - P.cH)) ∧
    (P.vH - P.cH ≤ P.vL - P.cL →
      transparentProfit P .L .L P.vL P.vL = 2 * (P.vL - P.cL)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hM m1 m2 p1 p2
    have key : ∀ (m : Product) (p : ℝ),
        (if p ≤ m.value P then (1 : ℝ) else 0) * (p - m.unitCost P) ≤
          max (P.vH - P.cH) (P.vL - P.cL) := by
      intro m p
      split_ifs with h
      · rw [one_mul]
        have hm : m.value P - m.unitCost P ≤ max (P.vH - P.cH) (P.vL - P.cL) := by
          cases m
          · exact le_max_left _ _
          · exact le_max_right _ _
        linarith
      · rw [zero_mul]; exact hM
    unfold transparentProfit
    linarith [key m1 p1, key m2 p2]
  · intro _
    simp only [transparentProfit, Product.value, Product.unitCost, le_refl, ↓reduceIte, one_mul]
    ring
  · intro _
    simp only [transparentProfit, Product.value, Product.unitCost, le_refl, ↓reduceIte, one_mul]
    ring
