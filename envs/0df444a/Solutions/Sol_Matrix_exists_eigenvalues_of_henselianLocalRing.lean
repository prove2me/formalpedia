-- Prove2me | solution 1 for Matrix.exists_eigenvalues_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/55f5b59b-cc2e-59f3-9dca-b34a52fb4f17

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_exists_eigenvalues_of_henselianLocalRing

theorem solution {A : Type*} [CommRing A] [IsLocalRing A]
    [HenselianLocalRing A] (M : Matrix (Fin 2) (Fin 2) A) {α β : IsLocalRing.ResidueField A}
    (hne : α ≠ β) (htr : IsLocalRing.residue A M.trace = α + β)
    (hdet : IsLocalRing.residue A M.det = α * β) :
    ∃ a b : A, M.trace = a + b ∧ M.det = a * b ∧ IsUnit (a - b) ∧
      IsLocalRing.residue A a = α ∧ IsLocalRing.residue A b = β := by
  open Polynomial IsLocalRing in
  obtain ⟨a₀, ha₀⟩ := residue_surjective (R := A) α
  set f : A[X] := X ^ 2 - (C M.trace * X + C (-M.det)) with hf
  have hmonic : f.Monic := by
    rw [hf]
    refine monic_X_pow_sub (lt_of_le_of_lt degree_linear_le ?_)
    exact_mod_cast one_lt_two
  have hevalf : ∀ x : A, f.eval x = x ^ 2 - M.trace * x + M.det := by
    intro x
    rw [hf]
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    ring
  have heval : f.eval a₀ ∈ maximalIdeal A := by
    rw [← residue_eq_zero_iff, hevalf, map_add, map_sub, map_pow, map_mul, ha₀, htr, hdet]
    ring
  have hderiv : derivative f = C 2 * X - C M.trace := by
    rw [hf, derivative_sub, derivative_add, derivative_X_pow, derivative_C_mul,
      derivative_X, derivative_C]
    simp only [Nat.cast_ofNat, mul_one, add_zero]
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  have hderiveval : (derivative f).eval a₀ = 2 * a₀ - M.trace := by
    rw [hderiv]
    simp only [eval_sub, eval_mul, eval_C, eval_X]
  have h2 : residue A (2 : A) = 2 := map_ofNat (residue A) 2
  have hunit : IsUnit ((derivative f).eval a₀) := by
    rw [← notMem_maximalIdeal, ← residue_eq_zero_iff, hderiveval]
    intro hcontra
    apply sub_ne_zero.mpr hne
    rw [map_sub, map_mul, ha₀, htr, h2] at hcontra
    linear_combination hcontra
  obtain ⟨a, hroot, hmem⟩ := HenselianLocalRing.is_henselian f hmonic a₀ heval hunit
  have haα : residue A a = α := by
    have h := (residue_eq_zero_iff (a - a₀)).mpr hmem
    rw [map_sub, sub_eq_zero] at h
    rw [h, ha₀]
  have hrooteq : a ^ 2 - M.trace * a + M.det = 0 := by
    have h : f.eval a = 0 := hroot
    rwa [hevalf] at h
  refine ⟨a, M.trace - a, by ring, ?_, ?_, haα, ?_⟩
  · linear_combination hrooteq
  · rw [← notMem_maximalIdeal, ← residue_eq_zero_iff]
    intro hcontra
    apply sub_ne_zero.mpr hne
    rw [map_sub, map_sub, haα, htr] at hcontra
    linear_combination hcontra
  · rw [map_sub, haα, htr]
    ring

end S_Matrix_exists_eigenvalues_of_henselianLocalRing
end P2MW
export P2MW.S_Matrix_exists_eigenvalues_of_henselianLocalRing (solution)
