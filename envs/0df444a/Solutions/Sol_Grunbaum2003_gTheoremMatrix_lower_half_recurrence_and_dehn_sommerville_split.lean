-- Prove2me | solution 1 for Grunbaum2003.gTheoremMatrix_lower_half_recurrence_and_dehn_sommerville_split
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:02:51.209189+00:00
-- url     : https://prove2.me/submissions/1838270d-ec58-473f-b49b-6c14508fb943

import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_gTheoremMatrix
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
private lemma gTheoremMatrix_prefix_sum_eq_of_le_half (d : ℕ) (g : ℕ → ℕ) (k : ℕ) (hk : k ≤ d / 2) :
    ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i k =
      (∑ i ∈ Finset.range k, (g i : ℤ) * gTheoremMatrix d i k) + (g k : ℤ) := by
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : k + 1 ≤ d / 2 + 1)]
  have hTail : ∑ i ∈ Finset.Ico (k + 1) (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i k = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_Ico] at hi
    rw [gTheoremMatrix_zero_of_lt d i k (by omega) (by omega), mul_zero]
  rw [hTail, add_zero, Finset.sum_range_succ, gTheoremMatrix_diag_eq_one d k hk, mul_one]

/-- Row `0` of `gTheoremMatrix d` is `Nat.choose (d + 1) k` for `k ≤ d`. -/
private lemma gTheoremMatrix_row_zero (d k : ℕ) (hkd : k ≤ d) :
    gTheoremMatrix d 0 k = (Nat.choose (d + 1) k : ℤ) := by
  unfold gTheoremMatrix
  have h0 : Nat.choose 0 (d + 1 - k) = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  have hsymm : Nat.choose (d + 1) (d + 1 - k) = Nat.choose (d + 1) k := by
    have hsub : d + 1 - (d + 1 - k) = k := by omega
    rw [← Nat.choose_symm (by omega : d + 1 - k ≤ d + 1), hsub]
  simp [h0, hsymm]

private lemma gTheoremMatrix_row_one_lt {d k : ℕ} (hk_lt : k < d) :
    gTheoremMatrix d 1 k = (Nat.choose d (d + 1 - k) : ℤ) := by
  unfold gTheoremMatrix
  have hsub : d + 1 - 1 = d := Nat.add_sub_cancel d 1
  have hgt : 1 < d + 1 - k := by omega
  have hchoose_zero : Nat.choose 1 (d + 1 - k) = 0 := Nat.choose_eq_zero_of_lt hgt
  rw [hsub, hchoose_zero]
  ring

private lemma gTheoremMatrix_row_one_top {d : ℕ} (_hd : 1 ≤ d) :
    gTheoremMatrix d 1 d = (d : ℤ) - 1 := by
  unfold gTheoremMatrix
  have hsub1 : d + 1 - 1 = d := Nat.add_sub_cancel d 1
  have hsub2 : d + 1 - d = 1 := by omega
  rw [hsub1, hsub2, Nat.choose_one_right, Nat.choose_self]
  ring

private lemma gTheoremMatrix_col_top {d i : ℕ} (hi : i ≤ d + 1) :
    gTheoremMatrix d i d = (d + 1 : ℤ) - 2 * (i : ℤ) := by
  unfold gTheoremMatrix
  have hsub : d + 1 - d = 1 := by omega
  rw [hsub, Nat.choose_one_right, Nat.choose_one_right]
  omega

private lemma two_mul_choose_two_int (n : ℕ) :
    2 * (Nat.choose n 2 : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
  have h_even : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
  have h_mul : 2 * Nat.choose n 2 = n * (n - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' h_even
  rcases n with _ | n
  · simp
  · have h_mul' : 2 * Nat.choose (n + 1) 2 = (n + 1) * n := by
      simpa using h_mul
    have h_int : (2 * Nat.choose (n + 1) 2 : ℤ) = ((n + 1) * n : ℤ) := by
      exact_mod_cast h_mul'
    push_cast at h_int ⊢
    linarith

private lemma gTheoremMatrix_top_two_columns_double_counting {d i : ℕ} (_hd : 2 ≤ d) (hi : i ≤ d + 1) :
    2 * gTheoremMatrix d i (d - 1) = (d : ℤ) * gTheoremMatrix d i d := by
  rw [gTheoremMatrix_col_top hi]
  unfold gTheoremMatrix
  have hsub : d + 1 - (d - 1) = 2 := by omega
  rw [hsub]
  have h1 := two_mul_choose_two_int (d + 1 - i)
  have h2 := two_mul_choose_two_int i
  have hcast : ((d + 1 - i : ℕ) : ℤ) = (d : ℤ) + 1 - (i : ℤ) := by omega
  rw [hcast] at h1
  linarith


theorem solution (d : ℕ) (hd : 4 ≤ d) :
    (∀ (P : Set (Fin d → ℝ)) (g : ℕ → ℕ),
      (∀ (k : ℕ), 1 ≤ k → k ≤ d / 2 →
        (g k : ℤ) = (faceCount P (k - 1) : ℤ) -
          ∑ i ∈ Finset.range k, (g i : ℤ) * gTheoremMatrix d i k) →
      (∀ (j : Fin d), d / 2 < j.succ.val →
        (faceCount P j.val : ℤ) =
          ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) →
      ∀ (j : Fin d),
        (faceCount P j.val : ℤ) =
          ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) ∧
    (∀ (P : Set (Fin d → ℝ)) (g : ℕ → ℕ),
      IsMSequence (d / 2) g →
      (∀ (j : Fin d),
        (faceCount P j.val : ℤ) =
          ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) →
      faceCount P 0 = d + 1 + g 1 ∧
      faceCount P 1 = Nat.choose (d + 1) 2 + d * g 1 + g 2 ∧
      2 * faceCount P (d - 2) = d * faceCount P (d - 1)) := by
  have hPref := gTheoremMatrix_prefix_sum_eq_of_le_half d
  have hRow0 := gTheoremMatrix_row_zero d
  refine ⟨?_, ?_⟩
  · intro P g hLow hHigh j
    have hj_succ : j.succ.val = j.val + 1 := Fin.val_succ j
    by_cases hj : j.succ.val ≤ d / 2
    · have h1 : 1 ≤ j.succ.val := by omega
      have hRec := hLow j.succ.val h1 hj
      have hSub : j.succ.val - 1 = j.val := by omega
      rw [hSub] at hRec
      rw [hPref g j.succ.val hj]
      linarith
    · exact hHigh j (by omega)
  · intro P g hg hRep
    have hg0 : g 0 = 1 := hg.1
    have hj0 := hRep ⟨0, by omega⟩
    change (faceCount P 0 : ℤ) =
      ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i 1 at hj0
    rw [hPref g 1 (by omega), Finset.sum_range_one,
      hg0, Nat.cast_one, one_mul, hRow0 1 (by omega), Nat.choose_one_right] at hj0
    have hV : faceCount P 0 = d + 1 + g 1 := by omega
    have hFd2 := hRep ⟨d - 2, by omega⟩
    have hFd1 := hRep ⟨d - 1, by omega⟩
    have hsucc_d2 : (⟨d - 2, by omega⟩ : Fin d).succ.val = d - 1 := by
      change (d - 2) + 1 = d - 1; omega
    have hsucc_d1 : (⟨d - 1, by omega⟩ : Fin d).succ.val = d := by
      change (d - 1) + 1 = d; omega
    rw [hsucc_d2] at hFd2
    rw [hsucc_d1] at hFd1
    have hDouble_int : 2 * (faceCount P (d - 2) : ℤ) = (d : ℤ) * (faceCount P (d - 1) : ℤ) := by
      rw [hFd2, hFd1, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi_le : i ≤ d + 1 := by
        have := Finset.mem_range.1 hi
        omega
      have hCol := gTheoremMatrix_top_two_columns_double_counting (by omega : 2 ≤ d) hi_le
      calc
        2 * ((g i : ℤ) * gTheoremMatrix d i (d - 1))
            = (g i : ℤ) * (2 * gTheoremMatrix d i (d - 1)) := by ring
        _ = (g i : ℤ) * ((d : ℤ) * gTheoremMatrix d i d) := by rw [hCol]
        _ = (d : ℤ) * ((g i : ℤ) * gTheoremMatrix d i d) := by ring
    have hDouble : 2 * faceCount P (d - 2) = d * faceCount P (d - 1) := by exact_mod_cast hDouble_int
    have hj1 := hRep ⟨1, by omega⟩
    change (faceCount P 1 : ℤ) =
      ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i 2 at hj1
    rw [hPref g 2 (by omega), Finset.sum_range_succ, Finset.sum_range_one,
        hg0, Nat.cast_one, one_mul, hRow0 2 (by omega)] at hj1
    have hM12 : gTheoremMatrix d 1 2 = (d : ℤ) := by
      have h1 := gTheoremMatrix_row_one_lt (d := d) (k := 2) (by omega)
      have hsymm : Nat.choose d (d + 1 - 2) = d := by
        have hsub : d - (d + 1 - 2) = 1 := by omega
        rw [← Nat.choose_symm (by omega : d + 1 - 2 ≤ d), hsub, Nat.choose_one_right]
      rw [hsymm] at h1
      exact h1
    rw [hM12] at hj1
    refine ⟨hV, ?_, hDouble⟩
    have hcast : (faceCount P 1 : ℤ) = ((Nat.choose (d + 1) 2 + d * g 1 + g 2 : ℕ) : ℤ) := by
      push_cast
      linarith
    exact Nat.cast_injective hcast

