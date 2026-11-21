-- Prove2me | solution 1 for MomentSearch.rakhmanov_interpolation_kernel
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-20T23:15:39.100215+00:00
-- url     : https://prove2.me/submissions/46cc8e26-bbb7-48d7-94bf-4ab412587660

import Mathlib
import Theorems.Thm_MomentSearch_rakhmanov_weighted_grid_basis
import Theorems.Thm_MomentSearch_rakhmanov_equilibrium_multiplier

open scoped BigOperators

theorem solution :
    ∃ A : ℝ, 0 < A ∧
      ∀ N k : ℕ, 1 ≤ k → k < N →
      ∀ P : Polynomial ℝ, P.natDegree ≤ k →
      (∀ j : ℕ, 1 ≤ j → j ≤ N → |P.eval (-1 + (2 * (j : ℝ) - 1) / (N : ℝ))| ≤ 1) →
      ∀ r : ℝ, r = Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2) →
      ∀ x : ℝ, -r < x → x < r →
      ∃ M y : ℝ, 0 < M ∧ M ≤ (N : ℝ) / 2 ∧ |x - y| ≤ 2 / M ∧
        (N : ℝ) / Real.pi * Real.arctan ((N : ℝ) / (k : ℝ) *
          Real.sqrt (r ^ 2 - x ^ 2)) ≤ M ∧
        |P.eval x| ≤ A * (∑ j ∈ Finset.Icc 1 N,
          1 / (max 1 ((N : ℝ) * |(-1 + (2 * (j : ℝ) - 1) / (N : ℝ)) - x|) *
            max 1 (M * |(-1 + (2 * (j : ℝ) - 1) / (N : ℝ)) - y|))) := by
  obtain ⟨A, hA, hbasis⟩ := MomentSearch.rakhmanov_weighted_grid_basis
  obtain ⟨B, hB, hmult⟩ := MomentSearch.rakhmanov_equilibrium_multiplier
  refine ⟨A * B, mul_pos hA hB, ?_⟩
  intro N k hk hkN P hP hgrid r hr x hxl hxr
  have hN : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hrle : r ≤ 1 := by
    rw [hr]
    exact Real.sqrt_le_one.mpr (by linarith [show 0 ≤ (k : ℝ) ^ 2 / (N : ℝ) ^ 2 by positivity])
  have hx : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, hxr.le.trans hrle⟩
  obtain ⟨M, y, H, hM, hMN, hxy, hμ, hH, hHx, hHgrid⟩ :=
    hmult N k hk hkN r hr x hxl hxr
  refine ⟨M, y, hM, hMN, hxy, hμ, ?_⟩
  let s := Finset.Icc 1 N
  let ζ (j : ℕ) : ℝ := -1 + (2 * (j : ℝ) - 1) / (N : ℝ)
  let w (z : ℝ) : ℝ := Real.exp (-(N : ℝ) / 2 *
    ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)))
  let K₁ (j : ℕ) : ℝ := max 1 ((N : ℝ) * |ζ j - x|)
  let K₂ (j : ℕ) : ℝ := max 1 (M * |ζ j - y|)
  have hinj : Set.InjOn ζ ↑s := by
    intro i _ j _ hij
    have hscaled : (2 * (i : ℝ) - 1) / (N : ℝ) =
        (2 * (j : ℝ) - 1) / (N : ℝ) := by dsimp [ζ] at hij; linarith
    have hu := congrArg (fun a : ℝ => a * (N : ℝ)) hscaled
    simp only [div_mul_cancel₀ _ hNr.ne'] at hu
    have hcast : (i : ℝ) = (j : ℝ) := by linarith
    exact_mod_cast hcast
  have hs : s.card = N := by simp [s, Nat.card_Icc]
  have hdeg : (P * H).degree < s.card := by
    refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    have hh := Polynomial.natDegree_mul_le (p := P) (q := H)
    rw [hs]
    exact_mod_cast (show (P * H).natDegree < N by omega)
  have hinter := Lagrange.eq_interpolate hinj hdeg
  have heval :
      P.eval x * H.eval x =
        ∑ j ∈ s, (P.eval (ζ j) * H.eval (ζ j)) * (Lagrange.basis s ζ j).eval x := by
    simpa only [Polynomial.eval_mul, Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
      Polynomial.eval_C] using congrArg (Polynomial.eval x) hinter
  have hw (z : ℝ) : 0 < w z := Real.exp_pos _
  have hK₁ (j : ℕ) : 0 < K₁ j := zero_lt_one.trans_le (le_max_left _ _)
  have hK₂ (j : ℕ) : 0 < K₂ j := zero_lt_one.trans_le (le_max_left _ _)
  have hHxpos : 0 < |H.eval x| := abs_pos.mpr hHx
  have hterm (j : ℕ) (hj : j ∈ s) :
      |H.eval (ζ j)| * |(Lagrange.basis s ζ j).eval x| ≤
        (A * B * |H.eval x|) * (1 / (K₁ j * K₂ j)) := by
    have h₁ : |(Lagrange.basis s ζ j).eval x| ≤ A * (w (ζ j) / w x) / K₁ j :=
      hbasis N hN x hx j hj
    have h₂ : |H.eval (ζ j)| ≤ B * |H.eval x| * (w x / w (ζ j)) / K₂ j :=
      hHgrid j hj
    calc
      _ ≤ (B * |H.eval x| * (w x / w (ζ j)) / K₂ j) *
          (A * (w (ζ j) / w x) / K₁ j) :=
        mul_le_mul h₂ h₁ (abs_nonneg _) (by have := hw x; have := hw (ζ j); have := hK₂ j; positivity)
      _ = _ := by
        field_simp [(hw x).ne', (hw (ζ j)).ne', (hK₁ j).ne', (hK₂ j).ne']
  have habs : |P.eval x| * |H.eval x| ≤
      (A * B * |H.eval x|) * (∑ j ∈ s, 1 / (K₁ j * K₂ j)) := by
    calc
      _ = |∑ j ∈ s, (P.eval (ζ j) * H.eval (ζ j)) * (Lagrange.basis s ζ j).eval x| := by
        rw [← abs_mul, heval]
      _ ≤ ∑ j ∈ s, |(P.eval (ζ j) * H.eval (ζ j)) * (Lagrange.basis s ζ j).eval x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ s, (A * B * |H.eval x|) * (1 / (K₁ j * K₂ j)) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_mul]
        have hp := hgrid j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
        refine le_trans (b := |H.eval (ζ j)| * |(Lagrange.basis s ζ j).eval x|) ?_ (hterm j hj)
        rw [mul_assoc]
        exact mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hp
      _ = _ := by rw [Finset.mul_sum]
  change |P.eval x| ≤ A * B * (∑ j ∈ s, 1 / (K₁ j * K₂ j))
  apply (mul_le_mul_iff_left₀ hHxpos).mp
  calc
    _ ≤ (A * B * |H.eval x|) * (∑ j ∈ s, 1 / (K₁ j * K₂ j)) := habs
    _ = _ := by ring
