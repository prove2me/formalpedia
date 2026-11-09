-- Prove2me | solution 1 for Grunbaum2003.gTheoremMatrix_lower_half_integer_coordinates_exist_unique
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:07:09.950474+00:00
-- url     : https://prove2.me/submissions/5ced030c-ce01-42a2-8236-bc6252eccaf1

import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped BigOperators
open Grunbaum2003

/-- Above the main diagonal (`k < i ≤ d / 2`), Björner's matrix `gTheoremMatrix d i k` vanishes. -/
private lemma gTheoremMatrix_zero_of_lt (d i k : ℕ) (hki : k < i) (hi : i ≤ d / 2) :
    gTheoremMatrix d i k = 0 := by
  unfold gTheoremMatrix
  have h1 : Nat.choose (d + 1 - i) (d + 1 - k) = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  have h2 : Nat.choose i (d + 1 - k) = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  simp [h1, h2]

/-- On the main diagonal (`0 ≤ k ≤ d / 2`), Björner's matrix `gTheoremMatrix d k k` equals `1`. -/
private lemma gTheoremMatrix_diag_eq_one (d k : ℕ) (hk : k ≤ d / 2) :
    gTheoremMatrix d k k = 1 := by
  unfold gTheoremMatrix
  have h2 : Nat.choose k (d + 1 - k) = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  simp [h2]

/-- Unit upper-triangular evaluation of `∑ i ∈ range (d / 2 + 1), g i * gTheoremMatrix d i k`
for `0 ≤ k ≤ d / 2`. -/
private lemma gTheoremMatrix_prefix_sum_eq_of_le_half (d : ℕ) (g : ℕ → ℤ) (k : ℕ) (hk : k ≤ d / 2) :
    ∑ i ∈ Finset.range (d / 2 + 1), g i * gTheoremMatrix d i k =
      (∑ i ∈ Finset.range k, g i * gTheoremMatrix d i k) + g k := by
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : k + 1 ≤ d / 2 + 1)]
  have hTail : ∑ i ∈ Finset.Ico (k + 1) (d / 2 + 1), g i * gTheoremMatrix d i k = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_Ico] at hi
    rw [gTheoremMatrix_zero_of_lt d i k (by omega) (by omega), mul_zero]
  rw [hTail, add_zero, Finset.sum_range_succ, gTheoremMatrix_diag_eq_one d k hk, mul_one]


/-- The lower-half matrix coordinates are determined uniquely, over the integers. -/
private theorem coordinates_unique (d : ℕ) (g h : ℕ → ℤ)
    (hEq : ∀ k : ℕ, k ≤ d / 2 →
      ∑ i ∈ Finset.range (d / 2 + 1), g i * gTheoremMatrix d i k =
      ∑ i ∈ Finset.range (d / 2 + 1), h i * gTheoremMatrix d i k) :
    ∀ k : ℕ, k ≤ d / 2 → g k = h k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    have hEqk := hEq k hk
    rw [gTheoremMatrix_prefix_sum_eq_of_le_half d g k hk,
      gTheoremMatrix_prefix_sum_eq_of_le_half d h k hk] at hEqk
    have hSum : ∑ i ∈ Finset.range k, g i * gTheoremMatrix d i k =
        ∑ i ∈ Finset.range k, h i * gTheoremMatrix d i k := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hik : i < k := Finset.mem_range.1 hi
      rw [ih i hik (by omega)]
    omega

/-- Integer existence and bounded uniqueness for the lower-half Björner transform. -/
theorem solution (d : ℕ) :
    (∀ f : ℕ → ℤ, ∃ g : ℕ → ℤ, ∀ k : ℕ, k ≤ d / 2 →
      ∑ i ∈ Finset.range (d / 2 + 1), g i * gTheoremMatrix d i k = f k) ∧
    (∀ g h : ℕ → ℤ,
      (∀ k : ℕ, k ≤ d / 2 →
        ∑ i ∈ Finset.range (d / 2 + 1), g i * gTheoremMatrix d i k =
        ∑ i ∈ Finset.range (d / 2 + 1), h i * gTheoremMatrix d i k) →
      ∀ k : ℕ, k ≤ d / 2 → g k = h k) := by
  refine ⟨?_, coordinates_unique d⟩
  intro f
  let step : (k : ℕ) → ((i : ℕ) → i < k → ℤ) → ℤ := fun k prev =>
    f k - ∑ i : Fin k, prev i.val i.isLt * gTheoremMatrix d i.val k
  let g : ℕ → ℤ := Nat.strongRec (motive := fun _ => ℤ) step
  have hrec (k : ℕ) : g k = f k - ∑ i ∈ Finset.range k, g i * gTheoremMatrix d i k := by
    change Nat.strongRec (motive := fun _ => ℤ) step k = _
    rw [Nat.strongRec_eq]
    change f k - (∑ i : Fin k, g i.val * gTheoremMatrix d i.val k) = _
    rw [Fin.sum_univ_eq_sum_range (fun i => g i * gTheoremMatrix d i k) k]
  refine ⟨g, ?_⟩
  intro k hk
  rw [gTheoremMatrix_prefix_sum_eq_of_le_half d g k hk]
  have hr := hrec k
  omega

