-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.between_mul_e
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T14:57:51.699574+00:00
-- url     : https://prove2.me/submissions/eb3cf49a-f5f0-478b-913f-5a2d006825c2

import Mathlib

theorem solution {a b y x L U : ℝ} (hy : a ≤ y ∧ y ≤ b)
    (ha : L ≤ x * a ∧ x * a ≤ U) (hb : L ≤ x * b ∧ x * b ≤ U) :
    L ≤ x * y ∧ x * y ≤ U := by
  rcases hy with ⟨hya, hyb⟩
  rcases ha with ⟨haL, haU⟩
  rcases hb with ⟨hbL, hbU⟩
  by_cases hx : 0 ≤ x
  · have h1 : 0 ≤ x * (y - a) := mul_nonneg hx (sub_nonneg.mpr hya)
    have h2 : 0 ≤ x * (b - y) := mul_nonneg hx (sub_nonneg.mpr hyb)
    constructor <;> nlinarith
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have h1 : x * (y - a) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hx' (sub_nonneg.mpr hya)
    have h2 : x * (b - y) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hx' (sub_nonneg.mpr hyb)
    constructor <;> nlinarith
