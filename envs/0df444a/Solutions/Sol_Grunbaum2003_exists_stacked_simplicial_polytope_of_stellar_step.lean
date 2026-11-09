-- Prove2me | solution 1 for Grunbaum2003.exists_stacked_simplicial_polytope_of_stellar_step
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T02:13:49.366191+00:00
-- url     : https://prove2.me/submissions/f7d7764d-ca0e-4db2-b778-f852299dc4f4

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Theorems.Thm_Grunbaum2003_exposed_edge_pair_and_simplex_faceCount_choose
import Theorems.Thm_Grunbaum2003_gTheoremMatrix_row_one_top_columns_and_g2_zero_sum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

open Grunbaum2003

lemma gTheoremMatrix_row_one_eq_stellar_increment {d : ℕ} (hd : 1 ≤ d) (j : Fin d) :
    gTheoremMatrix d 1 j.succ.val =
      if j.val + 1 < d then (Nat.choose d j.val : ℤ) else (d : ℤ) - 1 := by
  have hRow1 := Grunbaum2003.gTheoremMatrix_row_one_top_columns_and_g2_zero_sum
  change gTheoremMatrix d 1 (j.val + 1) = _
  split_ifs with hlt
  · rw [hRow1.1 hlt]
    have hsub : d + 1 - (j.val + 1) = d - j.val := by omega
    rw [hsub, Nat.choose_symm (by omega : j.val ≤ d)]
  · have heq : j.val + 1 = d := by omega
    rw [heq, hRow1.2.1 hd]

lemma exists_stacked_simplicial_polytope_of_stellar_step_aux (d : ℕ) (hd : 4 ≤ d)
    (hStep : ∀ P : Set (Fin d → ℝ), IsSimplicialDPolytope P →
      ∃ P' : Set (Fin d → ℝ), IsSimplicialDPolytope P' ∧
        (∀ j : Fin d, j.val + 1 < d → faceCount P' j.val = faceCount P j.val + Nat.choose d j.val) ∧
        faceCount P' (d - 1) = faceCount P (d - 1) + (d - 1)) :
    ∀ n : ℕ, ∃ P : Set (Fin d → ℝ), IsSimplicialDPolytope P ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        (Nat.choose (d + 1) j.succ.val : ℤ) + (n : ℤ) * gTheoremMatrix d 1 j.succ.val := by
  intro n
  induction n with
  | zero =>
    obtain ⟨P₀, hP₀, hF₀⟩ :=
      Grunbaum2003.exposed_edge_pair_and_simplex_faceCount_choose.2.2.2 d
    refine ⟨P₀, hP₀, fun j => ?_⟩
    rw [hF₀ j.val]
    simp [Fin.val_succ]
  | succ n ih =>
    obtain ⟨P, hP, hF⟩ := ih
    obtain ⟨P', hP', hLow, hTop⟩ := hStep P hP
    refine ⟨P', hP', fun j => ?_⟩
    have hInc := gTheoremMatrix_row_one_eq_stellar_increment (by omega : 1 ≤ d) j
    by_cases hlt : j.val + 1 < d
    · have h1 := hLow j hlt
      have hInc_lt : gTheoremMatrix d 1 j.succ.val = (Nat.choose d j.val : ℤ) := by
        rw [hInc, if_pos hlt]
      have h1_int : (faceCount P' j.val : ℤ) = (faceCount P j.val : ℤ) + (Nat.choose d j.val : ℤ) := by
        exact_mod_cast h1
      rw [h1_int, hF j, hInc_lt]
      push_cast
      ring
    · have hj_eq : j.val = d - 1 := by omega
      have h1 : faceCount P' j.val = faceCount P j.val + (d - 1) := by
        rw [hj_eq, hTop]
      have hInc_top : gTheoremMatrix d 1 j.succ.val = (d : ℤ) - 1 := by
        rw [hInc, if_neg hlt]
      have h1_int : (faceCount P' j.val : ℤ) = (faceCount P j.val : ℤ) + ((d : ℤ) - 1) := by
        have hcast : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
        rw [← hcast]
        exact_mod_cast h1
      rw [h1_int, hF j, hInc_top]
      push_cast
      ring

theorem solution :
    (∀ {d : ℕ}, 1 ≤ d → ∀ (j : Fin d),
      gTheoremMatrix d 1 j.succ.val =
        if j.val + 1 < d then (Nat.choose d j.val : ℤ) else (d : ℤ) - 1) ∧
    (∀ (d : ℕ), 4 ≤ d →
      (∀ P : Set (Fin d → ℝ), IsSimplicialDPolytope P →
        ∃ P' : Set (Fin d → ℝ), IsSimplicialDPolytope P' ∧
          (∀ j : Fin d, j.val + 1 < d → faceCount P' j.val = faceCount P j.val + Nat.choose d j.val) ∧
          faceCount P' (d - 1) = faceCount P (d - 1) + (d - 1)) →
      ∀ n : ℕ, ∃ P : Set (Fin d → ℝ), IsSimplicialDPolytope P ∧
        ∀ j : Fin d, (faceCount P j.val : ℤ) =
          (Nat.choose (d + 1) j.succ.val : ℤ) + (n : ℤ) * gTheoremMatrix d 1 j.succ.val) :=
  ⟨fun hd j => gTheoremMatrix_row_one_eq_stellar_increment hd j,
   fun d hd hStep n => exists_stacked_simplicial_polytope_of_stellar_step_aux d hd hStep n⟩
