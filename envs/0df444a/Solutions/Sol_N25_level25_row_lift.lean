-- Prove2me | solution 1 for N25.level25_row_lift
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:40:54.282424+00:00
-- url     : https://prove2.me/submissions/1d53367a-17f2-4a56-9db4-3fc3e6f074e3

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false

open scoped MatrixGroups

namespace N25

/-- A primitive residue row with unit second coordinate lifts through elementary matrices. -/
private theorem level25_row_lift_of_isUnit_right (c d : ZMod 25) (hd : IsUnit d) :
    ∃ A : SL(2, ℤ), (A 1 0 : ZMod 25) = c ∧ (A 1 1 : ZMod 25) = d := by
  obtain ⟨u, rfl⟩ := hd
  let x : ℤ := ((↑u⁻¹ : ZMod 25).val : ℤ)
  let y : ℤ := ((↑u : ZMod 25).val : ℤ)
  let t : ℤ := ((c * (↑u⁻¹ : ZMod 25)).val : ℤ)
  let U : ℤ → Matrix (Fin 2) (Fin 2) ℤ := fun n => !![1, n; 0, 1]
  let L : ℤ → Matrix (Fin 2) (Fin 2) ℤ := fun n => !![1, 0; n, 1]
  let W : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]
  have hx : (x : ZMod 25) = ↑u⁻¹ := by simp [x]
  have hy : (y : ZMod 25) = ↑u := by simp [y]
  have ht : (t : ZMod 25) = c * ↑u⁻¹ := by simp [t]
  refine ⟨⟨U x * L (-y) * U x * W * L t, by
    simp [Matrix.det_mul, U, L, W, Matrix.det_fin_two]
    <;> ring⟩, ?_, ?_⟩
  · change (((U x * L (-y) * U x * W * L t) 1 0 : ℤ) : ZMod 25) = c
    simp only [U, L, W, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    push_cast
    rw [hx, hy, ht]
    calc
      _ = 1 - (u : ZMod 25) * ↑u⁻¹ + c * ((u : ZMod 25) * ↑u⁻¹) := by ring
      _ = c := by simp
  · simp [U, L, W, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, hy]

/-- Every residue row having a unit coordinate is the bottom row of an integral matrix. -/
theorem _root_.solution (c d : ZMod 25) (h : IsUnit c ∨ IsUnit d) :
    ∃ A : SL(2, ℤ), (A 1 0 : ZMod 25) = c ∧ (A 1 1 : ZMod 25) = d := by
  rcases h with hc | hd
  · obtain ⟨A, hA, hB⟩ := level25_row_lift_of_isUnit_right (-d) c hc
    let W : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]
    refine ⟨⟨(A : Matrix (Fin 2) (Fin 2) ℤ) * W, by
      simp [Matrix.det_mul, W, Matrix.det_fin_two, Matrix.SpecialLinearGroup.det_coe]⟩, ?_, ?_⟩
    · simpa [W, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_two] using hB
    · simpa [W, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_two] using congrArg Neg.neg hA
  · exact level25_row_lift_of_isUnit_right c d hd

end N25
