-- Prove2me | solution 1 for OAI.CirculantHadamard.gram_eq_iff_autocorrelation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:49:38.675997+00:00
-- url     : https://prove2.me/submissions/429aa18e-4188-4792-a688-480b43712159

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge

open OAI OAI.CirculantHadamard
universe uR
open scoped BigOperators
variable {n : ℕ}
theorem gram_aux {n : ℕ} [NeZero n] {R : Type*} [CommRing R]
    (h : Fin n → R) (i a : Fin n) :
    (rowCirculant h * (rowCirculant h).transpose) i a =
      ∑ j, h j * h (j - (a - i)) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rowCirculant_apply]
  exact Fintype.sum_equiv (Equiv.subRight i) _ _ (fun k => by
    simp only [Equiv.subRight_apply]; congr 2; abel)


theorem solution [NeZero n] {R : Type uR} [CommRing R]
    (h : Fin n → R) :
    rowCirculant h * (rowCirculant h).transpose =
        (n : R) • (1 : Matrix (Fin n) (Fin n) R) ↔
      ∀ a : Fin n, ∑ j, h j * h (j - a) = if a = 0 then (n : R) else 0 := by
  constructor
  · intro H a
    have := congrFun (congrFun H 0) a
    rw [gram_aux, sub_zero] at this
    rw [this, Matrix.smul_apply, Matrix.one_apply]
    by_cases ha : a = 0
    · subst ha; simp
    · simp [ha, Ne.symm ha]
  · intro H
    ext i a
    rw [gram_aux, H, Matrix.smul_apply, Matrix.one_apply]
    by_cases ha : i = a
    · subst ha; simp
    · have : a - i ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
      simp [ha, this]
