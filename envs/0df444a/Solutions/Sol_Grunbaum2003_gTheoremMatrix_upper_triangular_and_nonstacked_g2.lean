-- Prove2me | solution 1 for Grunbaum2003.gTheoremMatrix_upper_triangular_and_nonstacked_g2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T02:38:50.289278+00:00
-- url     : https://prove2.me/submissions/d02b31bf-fc89-4255-b537-6780229a37ff

import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Theorems.Thm_Grunbaum2003_gTheoremMatrix_row_one_top_columns_and_g2_zero_sum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped BigOperators

open Grunbaum2003

/-- Above the main diagonal (`k < i ≤ d / 2`), Björner's matrix `gTheoremMatrix d i k` vanishes. -/
lemma gTheoremMatrix_zero_of_lt (d i k : ℕ) (hki : k < i) (hi : i ≤ d / 2) :
    gTheoremMatrix d i k = 0 := by
  unfold gTheoremMatrix
  have h1 : Nat.choose (d + 1 - i) (d + 1 - k) = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  have h2 : Nat.choose i (d + 1 - k) = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  simp [h1, h2]

/-- On the main diagonal (`0 ≤ k ≤ d / 2`), Björner's matrix `gTheoremMatrix d k k` equals `1`. -/
lemma gTheoremMatrix_diag_eq_one (d k : ℕ) (hk : k ≤ d / 2) :
    gTheoremMatrix d k k = 1 := by
  unfold gTheoremMatrix
  have h2 : Nat.choose k (d + 1 - k) = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  simp [h2]

/-- Unit upper-triangular evaluation of `∑ i ∈ range (d / 2 + 1), g i * gTheoremMatrix d i k`
for `0 ≤ k ≤ d / 2`. -/
lemma gTheoremMatrix_prefix_sum_eq_of_le_half (d : ℕ) (g : ℕ → ℕ) (k : ℕ) (hk : k ≤ d / 2) :
    ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i k =
      (∑ i ∈ Finset.range k, (g i : ℤ) * gTheoremMatrix d i k) + (g k : ℤ) := by
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : k + 1 ≤ d / 2 + 1)]
  have hTail : ∑ i ∈ Finset.Ico (k + 1) (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i k = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_Ico] at hi
    rw [gTheoremMatrix_zero_of_lt d i k (by omega) (by omega), mul_zero]
  rw [hTail, add_zero, Finset.sum_range_succ, gTheoremMatrix_diag_eq_one d k hk, mul_one]

/-- Row `0` of `gTheoremMatrix d` is `Nat.choose (d + 1) k` for `k ≤ d`. -/
lemma gTheoremMatrix_row_zero (d k : ℕ) (hkd : k ≤ d) :
    gTheoremMatrix d 0 k = (Nat.choose (d + 1) k : ℤ) := by
  unfold gTheoremMatrix
  have h0 : Nat.choose 0 (d + 1 - k) = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  have hsymm : Nat.choose (d + 1) (d + 1 - k) = Nat.choose (d + 1) k := by
    have hsub : d + 1 - (d + 1 - k) = k := by omega
    rw [← Nat.choose_symm (by omega : d + 1 - k ≤ d + 1), hsub]
  simp [h0, hsymm]

/-- Any `M`-sequence `g` representing the face counts of a non-stacked simplicial `d`-polytope `P`
(`d ≥ 4`, `d + 1 < faceCount P 0`) satisfies `g 0 = 1`, `g 1 = faceCount P 0 - (d + 1) > 0`,
`0 < g 2`, and `(g 2 : ℤ) = (faceCount P 1 : ℤ) - Nat.choose (d + 1) 2 - d * g 1`. -/
lemma nonstacked_mSequence_g1_g2_characterization (d : ℕ) (hd : 4 ≤ d)
    (P : Set (Fin d → ℝ)) (hV_gt : d + 1 < faceCount P 0)
    (hNonStacked : ¬ ∀ j : Fin d, (faceCount P j.val : ℤ) =
      (Nat.choose (d + 1) j.succ.val : ℤ) +
        ((faceCount P 0 - (d + 1) : ℕ) : ℤ) * gTheoremMatrix d 1 j.succ.val)
    (g : ℕ → ℕ) (hg : IsMSequence (d / 2) g)
    (hRep : ∀ j : Fin d, (faceCount P j.val : ℤ) =
      ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) :
    g 0 = 1 ∧
    g 1 = faceCount P 0 - (d + 1) ∧
    0 < g 1 ∧
    0 < g 2 ∧
    (g 2 : ℤ) = (faceCount P 1 : ℤ) - (Nat.choose (d + 1) 2 : ℤ) - (d : ℤ) * (g 1 : ℤ) := by
  have hBase := Grunbaum2003.gTheoremMatrix_row_one_top_columns_and_g2_zero_sum.2.2.2.2.2
    hd P g hg hRep
  have hg0 : g 0 = 1 := hBase.1
  have hV_eq : faceCount P 0 = d + 1 + g 1 := hBase.2.1
  have hg1 : g 1 = faceCount P 0 - (d + 1) := by omega
  have hg1_pos : 0 < g 1 := hBase.2.2.2 hV_gt
  have hg2_pos : 0 < g 2 := by
    by_contra hle
    have hg2_zero : g 2 = 0 := by omega
    have hRow1 := Grunbaum2003.gTheoremMatrix_row_one_top_columns_and_g2_zero_sum.2.2.2.2.1
      (by omega : 2 ≤ d) hg hg2_zero
    apply hNonStacked
    intro j
    rw [hRep j, hRow1 j, hg1]
  have hj1 := hRep ⟨1, by omega⟩
  change (faceCount P 1 : ℤ) =
    ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i 2 at hj1
  rw [gTheoremMatrix_prefix_sum_eq_of_le_half d g 2 (by omega),
      Finset.sum_range_succ, Finset.sum_range_one,
      hg0, Nat.cast_one, one_mul,
      gTheoremMatrix_row_zero d 2 (by omega)] at hj1
  have hM12 : gTheoremMatrix d 1 2 = (d : ℤ) := by
    have h1 := Grunbaum2003.gTheoremMatrix_row_one_top_columns_and_g2_zero_sum.1
      (d := d) (k := 2) (by omega)
    have hsymm : Nat.choose d (d + 1 - 2) = d := by
      have hsub : d - (d + 1 - 2) = 1 := by omega
      rw [← Nat.choose_symm (by omega : d + 1 - 2 ≤ d), hsub, Nat.choose_one_right]
    rw [hsymm] at h1
    exact h1
  rw [hM12] at hj1
  refine ⟨hg0, hg1, hg1_pos, hg2_pos, ?_⟩
  linarith

theorem solution (d : ℕ) (hd : 4 ≤ d) :
    (∀ (i k : ℕ), k < i → i ≤ d / 2 → gTheoremMatrix d i k = 0) ∧
    (∀ (k : ℕ), k ≤ d / 2 → gTheoremMatrix d k k = 1) ∧
    (∀ (g : ℕ → ℕ) (k : ℕ), k ≤ d / 2 →
      ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i k =
        (∑ i ∈ Finset.range k, (g i : ℤ) * gTheoremMatrix d i k) + (g k : ℤ)) ∧
    (∀ (k : ℕ), k ≤ d →
      gTheoremMatrix d 0 k = (Nat.choose (d + 1) k : ℤ)) ∧
    (∀ (P : Set (Fin d → ℝ)), d + 1 < faceCount P 0 →
      (¬ ∀ j : Fin d, (faceCount P j.val : ℤ) =
        (Nat.choose (d + 1) j.succ.val : ℤ) +
          ((faceCount P 0 - (d + 1) : ℕ) : ℤ) * gTheoremMatrix d 1 j.succ.val) →
      ∀ (g : ℕ → ℕ), IsMSequence (d / 2) g →
        (∀ j : Fin d, (faceCount P j.val : ℤ) =
          ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) →
        g 0 = 1 ∧
        g 1 = faceCount P 0 - (d + 1) ∧
        0 < g 1 ∧
        0 < g 2 ∧
        (g 2 : ℤ) = (faceCount P 1 : ℤ) - (Nat.choose (d + 1) 2 : ℤ) - (d : ℤ) * (g 1 : ℤ)) := by
  refine ⟨gTheoremMatrix_zero_of_lt d, gTheoremMatrix_diag_eq_one d,
    gTheoremMatrix_prefix_sum_eq_of_le_half d, gTheoremMatrix_row_zero d, ?_⟩
  intro P hV_gt hNonStacked g hg hRep
  exact nonstacked_mSequence_g1_g2_characterization d hd P hV_gt hNonStacked g hg hRep
