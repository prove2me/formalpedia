-- Prove2me | solution 1 for Grunbaum2003.gTheoremMatrix_row_one_top_columns_and_g2_zero_sum
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T02:01:01.784706+00:00
-- url     : https://prove2.me/submissions/a2607b92-0f77-4c12-8ed5-1a46b264cbcc

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Theorems.Thm_Grunbaum2003_gTheoremMatrix_columns_mSequence_and_simplex_realization
import Theorems.Thm_Grunbaum2003_g_theorem_simplex_and_zero_tail_characterization
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped BigOperators

open Grunbaum2003

lemma gTheoremMatrix_row_one_lt {d k : ℕ} (hk_lt : k < d) :
    gTheoremMatrix d 1 k = (Nat.choose d (d + 1 - k) : ℤ) := by
  unfold gTheoremMatrix
  have hsub : d + 1 - 1 = d := Nat.add_sub_cancel d 1
  have hgt : 1 < d + 1 - k := by omega
  have hchoose_zero : Nat.choose 1 (d + 1 - k) = 0 := Nat.choose_eq_zero_of_lt hgt
  rw [hsub, hchoose_zero]
  ring

lemma gTheoremMatrix_row_one_top {d : ℕ} (_hd : 1 ≤ d) :
    gTheoremMatrix d 1 d = (d : ℤ) - 1 := by
  unfold gTheoremMatrix
  have hsub1 : d + 1 - 1 = d := Nat.add_sub_cancel d 1
  have hsub2 : d + 1 - d = 1 := by omega
  rw [hsub1, hsub2, Nat.choose_one_right, Nat.choose_self]
  ring

lemma gTheoremMatrix_col_top {d i : ℕ} (hi : i ≤ d + 1) :
    gTheoremMatrix d i d = (d + 1 : ℤ) - 2 * (i : ℤ) := by
  unfold gTheoremMatrix
  have hsub : d + 1 - d = 1 := by omega
  rw [hsub, Nat.choose_one_right, Nat.choose_one_right]
  omega

lemma two_mul_choose_two_int (n : ℕ) :
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

lemma gTheoremMatrix_top_two_columns_double_counting {d i : ℕ} (_hd : 2 ≤ d) (hi : i ≤ d + 1) :
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

lemma gTheoremMatrix_sum_of_g2_eq_zero {d : ℕ} (hd : 2 ≤ d) {g : ℕ → ℕ}
    (hg : IsMSequence (d / 2) g) (hg2 : g 2 = 0) (j : Fin d) :
    ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val =
      (Nat.choose (d + 1) j.succ.val : ℤ) + (g 1 : ℤ) * gTheoremMatrix d 1 j.succ.val := by
  have hZero := Grunbaum2003.g_theorem_simplex_and_zero_tail_characterization.1 hg hg2
  have hBridge := Grunbaum2003.gTheoremMatrix_columns_mSequence_and_simplex_realization
  have _hd2_pos : 1 ≤ d / 2 := by omega
  have hSplit : Finset.range (d / 2 + 1) =
      insert 0 (insert 1 ((Finset.range (d / 2 + 1)).filter (fun i => 2 ≤ i))) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_filter]
    omega
  rw [hSplit, Finset.sum_insert, Finset.sum_insert]
  · have hTail : ∑ i ∈ (Finset.range (d / 2 + 1)).filter (fun i => 2 ≤ i),
        (g i : ℤ) * gTheoremMatrix d i j.succ.val = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      have hgi : g i = 0 := hZero i hi.2 (Nat.lt_succ_iff.1 hi.1)
      simp [hgi]
    rw [hTail, add_zero, hg.1, Int.ofNat_one, one_mul, hBridge.1 d j.succ]
  · simp
  · simp

lemma g_theorem_necessity_consequences {d : ℕ} (hd : 4 ≤ d) (P : Set (Fin d → ℝ))
    (g : ℕ → ℕ) (hg : IsMSequence (d / 2) g)
    (hF : ∀ j : Fin d, (faceCount P j.val : ℤ) =
      ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) :
    g 0 = 1 ∧
    faceCount P 0 = d + 1 + g 1 ∧
    2 * faceCount P (d - 2) = d * faceCount P (d - 1) ∧
    (d + 1 < faceCount P 0 → 0 < g 1) := by
  have hBridge := Grunbaum2003.gTheoremMatrix_columns_mSequence_and_simplex_realization
  have hd2 : 2 ≤ d := by omega
  have hCol1 := hBridge.2.2.1 d hd2 g hg.1
  have hF0 := hF ⟨0, by omega⟩
  change (faceCount P 0 : ℤ) = ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i 1 at hF0
  rw [hCol1] at hF0
  have hV_eq : faceCount P 0 = d + 1 + g 1 := by omega
  have hFd2 := hF ⟨d - 2, by omega⟩
  have hFd1 := hF ⟨d - 1, by omega⟩
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
    have hCol := gTheoremMatrix_top_two_columns_double_counting hd2 hi_le
    calc
      2 * ((g i : ℤ) * gTheoremMatrix d i (d - 1))
          = (g i : ℤ) * (2 * gTheoremMatrix d i (d - 1)) := by ring
      _ = (g i : ℤ) * ((d : ℤ) * gTheoremMatrix d i d) := by rw [hCol]
      _ = (d : ℤ) * ((g i : ℤ) * gTheoremMatrix d i d) := by ring
  have hDouble : 2 * faceCount P (d - 2) = d * faceCount P (d - 1) := by exact_mod_cast hDouble_int
  refine ⟨hg.1, hV_eq, hDouble, fun hgt => by omega⟩

theorem solution :
    (∀ {d k : ℕ}, k < d →
      gTheoremMatrix d 1 k = (Nat.choose d (d + 1 - k) : ℤ)) ∧
    (∀ {d : ℕ}, 1 ≤ d →
      gTheoremMatrix d 1 d = (d : ℤ) - 1) ∧
    (∀ {d i : ℕ}, i ≤ d + 1 →
      gTheoremMatrix d i d = (d + 1 : ℤ) - 2 * (i : ℤ)) ∧
    (∀ {d i : ℕ}, 2 ≤ d → i ≤ d + 1 →
      2 * gTheoremMatrix d i (d - 1) = (d : ℤ) * gTheoremMatrix d i d) ∧
    (∀ {d : ℕ}, 2 ≤ d → ∀ {g : ℕ → ℕ},
      IsMSequence (d / 2) g → g 2 = 0 → ∀ (j : Fin d),
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val =
          (Nat.choose (d + 1) j.succ.val : ℤ) + (g 1 : ℤ) * gTheoremMatrix d 1 j.succ.val) ∧
    (∀ {d : ℕ}, 4 ≤ d → ∀ (P : Set (Fin d → ℝ)) (g : ℕ → ℕ),
      IsMSequence (d / 2) g →
      (∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) →
      g 0 = 1 ∧
      faceCount P 0 = d + 1 + g 1 ∧
      2 * faceCount P (d - 2) = d * faceCount P (d - 1) ∧
      (d + 1 < faceCount P 0 → 0 < g 1)) :=
  ⟨fun hk => gTheoremMatrix_row_one_lt hk,
   fun hd => gTheoremMatrix_row_one_top hd,
   fun hi => gTheoremMatrix_col_top hi,
   fun hd hi => gTheoremMatrix_top_two_columns_double_counting hd hi,
   fun hd _ hg hg2 j => gTheoremMatrix_sum_of_g2_eq_zero hd hg hg2 j,
   fun hd P g hg hF => g_theorem_necessity_consequences hd P g hg hF⟩
