-- Prove2me | solution 1 for IllinoisBrick.Cartel.proposition_2b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T22:11:21.596206+00:00
-- url     : https://prove2.me/submissions/af941e82-da5e-483e-a22c-ae5a0595f669

import Mathlib
import Definitions.Def_IllinoisBrick_Cartel_Model
import Theorems.Thm_IllinoisBrick_Cartel_proposition_1
import Theorems.Thm_IllinoisBrick_Cartel_retailer_eq_linear

open IllinoisBrick.Cartel

theorem solution (a b c : ℝ) (h : Standing a b c) :
    ∃ v : Fin 2 → Terms, (∀ j, Admissible c Contract.WPFF (v j)) ∧
      (∃ q : Fin 2 → ℝ, IsRetailerEq a b c Contract.WPFF v q) ∧
      ∀ q qC : Fin 2 → ℝ, IsRetailerEq a b c Contract.WPFF v q →
        IsRetailerEq a b c Contract.WPFF (fun _ => competitiveTerms a b c Contract.WPFF) qC →
        IsCartel a b c Contract.WPFF v q qC := by
  obtain ⟨hb, hac⟩ := h
  set A := a - c with hA
  have hA0 : 0 < A := by linarith
  let vt : Terms := ⟨c + A / 4, 0, 0, -(A ^ 2 / (18 * b)), 0⟩
  have hadm : ∀ j : Fin 2, Admissible c Contract.WPFF ((fun _ => vt) j) := by
    intro j; simp [Admissible, vt]
  have hf : ∀ j : Fin 2, ((fun _ => vt) j).f ≤ 0 := by
    intro j
    show -(A ^ 2 / (18 * b)) ≤ 0
    have : 0 ≤ A ^ 2 / (18 * b) := div_nonneg (sq_nonneg _) (by linarith)
    linarith
  have hw : c + A / 4 < a := by linarith
  have hL := retailer_eq_linear a b c (c + A / 4) hb hw (fun _ => vt) hadm (fun _ => rfl) hf
  refine ⟨fun _ => vt, hadm, hL.1, ?_⟩
  intro q qC hq hqC
  have hP1 := (proposition_1 a b c ⟨hb, hac⟩ Contract.WPFF).2 qC hqC
  have hE := hL.2 q hq
  have haw : a - (c + A / 4) = 3 * A / 4 := by rw [hA]; ring
  constructor
  · intro j
    rw [(hP1 j).2.1]
    have hqj : q j = A / (4 * b) := by
      rw [(hE j).1, haw]; field_simp
    have hqpos : 0 < q j := by rw [hqj]; positivity
    simp only [manufacturerProfit, payment, vt]
    rw [if_pos hqpos, hqj]
    have e : (c + A / 4) * (A / (4 * b)) + -(A ^ 2 / (18 * b)) - c * (A / (4 * b)) =
        A ^ 2 / (144 * b) := by field_simp; ring
    rw [e]; positivity
  · intro i
    rw [(hP1 i).2.2, (hE i).2, haw]
    show (A) ^ 2 / (9 * b) ≤ (3 * A / 4) ^ 2 / (9 * b) - -(A ^ 2 / (18 * b))
    have h1 : (3 * A / 4) ^ 2 / (9 * b) - -(A ^ 2 / (18 * b)) - A ^ 2 / (9 * b) =
        A ^ 2 / (144 * b) := by field_simp; ring
    have h2 : 0 ≤ A ^ 2 / (144 * b) := by positivity
    linarith

