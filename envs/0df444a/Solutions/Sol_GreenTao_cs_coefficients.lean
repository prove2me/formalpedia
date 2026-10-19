-- Prove2me | solution 1 for GreenTao.cs_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T21:29:03.632752+00:00
-- url     : https://prove2.me/submissions/b3679310-860a-4b06-bd7c-6c6d4f9313a7

import Definitions.Def_GreenTao_ProgressionCS
import Mathlib

open GreenTao

private lemma coeff_nonzero (d : ℕ) (j : Fin (d + 1)) (i : Fin d) : csCoeff d j i ≠ 0 := by
  intro h
  apply j.succAbove_ne i
  apply Fin.ext
  dsimp [csCoeff] at h
  omega

private lemma coeff_injective (d : ℕ) (j : Fin (d + 1)) : Function.Injective (csCoeff d j) := by
  intro i l h
  apply (Fin.succAbove_right_injective (p := j))
  apply Fin.ext
  dsimp [csCoeff] at h
  omega

private lemma coeff_height (d : ℕ) (j : Fin (d + 1)) (i : Fin d) :
    (csCoeff d j i).natAbs ≤ d := by
  have h₁ := (j.succAbove i).isLt
  have h₂ := j.isLt
  dsimp [csCoeff]
  omega

private lemma fraction_height (a b : ℤ) (hb : b ≠ 0) :
    ((a : ℚ) / b).num.natAbs ≤ a.natAbs ∧ ((a : ℚ) / b).den ≤ b.natAbs := by
  obtain ⟨c, ha, hc⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den a hb
  have hc0 : c ≠ 0 := by
    intro h
    simp only [h, zero_mul] at hc
    exact hb hc
  have hcpos : 0 < c.natAbs := Int.natAbs_pos.mpr hc0
  constructor
  · conv_rhs => rw [ha, Int.natAbs_mul]
    exact Nat.le_mul_of_pos_left _ hcpos
  · have hh := congrArg Int.natAbs hc
    simp only [Int.natAbs_mul, Int.natAbs_natCast] at hh
    rw [hh]
    exact Nat.le_mul_of_pos_left _ hcpos

private lemma ratcoeff_fraction (d : ℕ) (j : Fin (d + 1)) (i l : Fin d) :
    csRatCoeff d j i l = ((csCoeff d j l - csCoeff d j i : ℤ) : ℚ) / (csCoeff d j l : ℚ) := by
  have h : (csCoeff d j l : ℚ) ≠ 0 := by exact_mod_cast coeff_nonzero d j l
  dsimp [csRatCoeff]
  push_cast
  field_simp

theorem solution (d : ℕ) (j : Fin (d + 1)) :
    (∀ i : Fin d, csCoeff d j i ≠ 0 ∧ (csCoeff d j i).natAbs ≤ d) ∧
    Function.Injective (csCoeff d j) ∧
    (∀ i l : Fin d, (csRatCoeff d j i l).num.natAbs ≤ d ∧ (csRatCoeff d j i l).den ≤ d) ∧
    (∀ i l : Fin d, csRatCoeff d j i l = 0 ↔ i = l) := by
  refine ⟨fun i => ⟨coeff_nonzero d j i, coeff_height d j i⟩, coeff_injective d j, ?_, ?_⟩
  · intro i l
    rw [ratcoeff_fraction]
    have hh := fraction_height (csCoeff d j l - csCoeff d j i) (csCoeff d j l) (coeff_nonzero d j l)
    constructor
    · apply hh.1.trans
      have h₁ := (j.succAbove i).isLt
      have h₂ := (j.succAbove l).isLt
      dsimp [csCoeff]
      omega
    · exact hh.2.trans (coeff_height d j l)
  · intro i l
    have h : (csCoeff d j l : ℚ) ≠ 0 := by exact_mod_cast coeff_nonzero d j l
    constructor
    · intro hh
      have hdiv : (csCoeff d j i : ℚ) / (csCoeff d j l : ℚ) = 1 :=
        (sub_eq_zero.mp hh).symm
      have heq : (csCoeff d j i : ℚ) = (csCoeff d j l : ℚ) := (div_eq_one_iff_eq h).mp hdiv
      apply coeff_injective d j
      exact_mod_cast heq
    · intro hh
      subst l
      simp [csRatCoeff, h]
