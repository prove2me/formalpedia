-- Prove2me | solution 1 for HardyFiveAxioms.qubitA_posDef_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T12:53:38.419728+00:00
-- url     : https://prove2.me/submissions/07e5c126-7326-4159-849f-369ce8f4892c

import Mathlib
import Definitions.Def_hardy2001_qubit

open HardyFiveAxioms in
theorem qubitA_det_eq_1e2ccb7f (a b c : ℝ) :
    (qubitA a b c).det =
      (4 * (a * b * (1 - a) * (1 - b)) - (c - (1 - a - b + 2 * a * b)) ^ 2) / 2 := by
  rw [Matrix.det_fin_three]
  simp [qubitA]
  ring

open HardyFiveAxioms Matrix in
theorem qubitA_quad_1e2ccb7f (a b c : ℝ) (v : Fin 3 → ℝ) :
    star v ⬝ᵥ (qubitA a b c *ᵥ v) =
      (1 / 2) * v 0 ^ 2 + (1 / 2) * v 1 ^ 2 + (1 / 2) * v 2 ^ 2
        + 2 * (a - 1 / 2) * v 0 * v 1 + 2 * (b - 1 / 2) * v 0 * v 2
        + 2 * (c - 1 / 2) * v 1 * v 2 := by
  simp [qubitA, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

open HardyFiveAxioms in
theorem qubitA_isHermitian_1e2ccb7f (a b c : ℝ) : (qubitA a b c).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qubitA]

open HardyFiveAxioms in
theorem solution (a b c : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) :
    (qubitA a b c).PosDef ↔ cMinus a b < c ∧ c < cPlus a b := by
  have hA : 0 ≤ a * (1 - a) := by
    have h1 : 0 ≤ 1 - a := by linarith
    positivity
  have hB : 0 ≤ b * (1 - b) := by
    have h1 : 0 ≤ 1 - b := by linarith
    positivity
  have hx : 0 ≤ a * b * (1 - a) * (1 - b) := by
    have : a * b * (1 - a) * (1 - b) = (a * (1 - a)) * (b * (1 - b)) := by ring
    rw [this]; positivity
  set s := Real.sqrt (a * b * (1 - a) * (1 - b)) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = a * b * (1 - a) * (1 - b) := Real.sq_sqrt hx
  rw [cMinus, cPlus, ← hs]
  set m := 1 - a - b + 2 * a * b with hm
  constructor
  · intro h
    have hd := h.det_pos
    rw [qubitA_det_eq_1e2ccb7f, ← hs2, ← hm] at hd
    have key : 4 * s ^ 2 - (c - m) ^ 2 = (2 * s - (c - m)) * (2 * s + (c - m)) := by ring
    have hd' : 0 < (2 * s - (c - m)) * (2 * s + (c - m)) := by rw [← key]; linarith
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hd' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · constructor <;> linarith
    · exfalso; linarith
  · rintro ⟨h1, h2⟩
    have hsp : 0 < s := by linarith
    have hprod : 0 < a * (1 - a) * (b * (1 - b)) := by
      have : a * (1 - a) * (b * (1 - b)) = s ^ 2 := by rw [hs2]; ring
      rw [this]; positivity
    have hA' : 0 < a * (1 - a) := by
      rcases hA.lt_or_eq with h | h
      · exact h
      · rw [← h] at hprod; simp at hprod
    set d1 := 2 * (a * (1 - a)) with hd1
    have hd1p : 0 < d1 := by positivity
    have hD : 0 < 4 * s ^ 2 - (c - m) ^ 2 := by
      have key : 4 * s ^ 2 - (c - m) ^ 2 = (2 * s - (c - m)) * (2 * s + (c - m)) := by ring
      rw [key]; apply mul_pos <;> linarith
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (qubitA_isHermitian_1e2ccb7f a b c) ?_
    intro v hv
    rw [qubitA_quad_1e2ccb7f]
    set q := (1 / 2) * v 0 ^ 2 + (1 / 2) * v 1 ^ 2 + (1 / 2) * v 2 ^ 2
        + 2 * (a - 1 / 2) * v 0 * v 1 + 2 * (b - 1 / 2) * v 0 * v 2
        + 2 * (c - 1 / 2) * v 1 * v 2 with hq
    have iden : d1 * q =
        d1 / 2 * (v 0 + 2 * (a - 1 / 2) * v 1 + 2 * (b - 1 / 2) * v 2) ^ 2
          + (d1 * v 1 + (c - m) * v 2) ^ 2
          + (4 * s ^ 2 - (c - m) ^ 2) * v 2 ^ 2 := by
      rw [hs2, hq, hd1, hm]; ring
    have n1 : 0 ≤ d1 / 2 * (v 0 + 2 * (a - 1 / 2) * v 1 + 2 * (b - 1 / 2) * v 2) ^ 2 :=
      mul_nonneg (by positivity) (sq_nonneg _)
    have n2 : 0 ≤ (d1 * v 1 + (c - m) * v 2) ^ 2 := sq_nonneg _
    have n3 : 0 ≤ (4 * s ^ 2 - (c - m) ^ 2) * v 2 ^ 2 := mul_nonneg hD.le (sq_nonneg _)
    have hpos : 0 < d1 * q := by
      rw [iden]
      by_cases h2 : v 2 = 0
      · by_cases h1 : v 1 = 0
        · have h0 : v 0 ≠ 0 := by
            intro h0; apply hv; ext i; fin_cases i <;> simp [h0, h1, h2]
          have hS : v 0 + 2 * (a - 1 / 2) * v 1 + 2 * (b - 1 / 2) * v 2 ≠ 0 := by
            rw [h1, h2]; simpa using h0
          have : 0 < d1 / 2 * (v 0 + 2 * (a - 1 / 2) * v 1 + 2 * (b - 1 / 2) * v 2) ^ 2 :=
            mul_pos (by positivity) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hS)))
          linarith
        · have hT : d1 * v 1 + (c - m) * v 2 ≠ 0 := by
            rw [h2, mul_zero, add_zero]; exact mul_ne_zero hd1p.ne' h1
          have : 0 < (d1 * v 1 + (c - m) * v 2) ^ 2 :=
            lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hT))
          linarith
      · have : 0 < (4 * s ^ 2 - (c - m) ^ 2) * v 2 ^ 2 :=
          mul_pos hD (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h2)))
        linarith
    exact pos_of_mul_pos_right hpos hd1p.le
