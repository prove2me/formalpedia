-- Prove2me | solution 1 for LinearMap.exists_apply_basis_eq_smul_of_mul_eq_pow_mul_of_toMatrix_sub_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/599e2826-66e4-5769-b98c-8509971d157f

import Mathlib
import Theorems.Thm_Matrix_apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_exists_apply_basis_eq_smul_of_mul_eq_pow_mul_of_toMatrix_sub_one_mem

set_option autoImplicit false

universe u v

open IsLocalRing

theorem solution {R : Type u} [CommRing R] [IsLocalRing R]
    (hH : ∀ x : R, (∀ n : ℕ, x ∈ IsLocalRing.maximalIdeal R ^ n) → x = 0)
    {V : Type v} [AddCommGroup V] [Module R V] (b : Module.Basis (Fin 2) R V) (Φ N : Module.End R V)
    {a d : R} {q : ℕ} (hΦ0 : Φ (b 0) = a • b 0) (hΦ1 : Φ (b 1) = d • b 1)
    (had : IsUnit (a - (q : R) * d)) (hda : IsUnit (d - (q : R) * a))
    (hN : ∀ i j, LinearMap.toMatrix b b N i j - (1 : Matrix (Fin 2) (Fin 2) R) i j ∈ IsLocalRing.maximalIdeal R)
    (hrel : Φ * N = N ^ q * Φ) :
    ∃ x y : R, IsUnit x ∧ IsUnit y ∧ N (b 0) = x • b 0 ∧ N (b 1) = y • b 1 := by
  classical
  set M := LinearMap.toMatrix b b N with hM
  have hΦm : LinearMap.toMatrix b b Φ = Matrix.diagonal ![a, d] := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    fin_cases j <;> fin_cases i <;> simp [hΦ0, hΦ1, Matrix.diagonal]
  have hrelm : Matrix.diagonal ![a, d] * M = M ^ q * Matrix.diagonal ![a, d] := by
    have h := congrArg (LinearMap.toMatrix b b) hrel
    rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, hΦm] at h
    have hp : ∀ n : ℕ, LinearMap.toMatrix b b (N ^ n) = M ^ n := by
      intro n
      induction n with
      | zero => rw [pow_zero, pow_zero]; exact LinearMap.toMatrix_one b
      | succ n ih => rw [pow_succ, pow_succ, LinearMap.toMatrix_mul, ih]
    rw [hp q] at h
    exact h
  obtain ⟨h01, h10⟩ :=
    Matrix.apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem hH had hda hN hrelm

  have hNb : ∀ j, N (b j) = ∑ i, M i j • b i := fun j => by
    have := (LinearMap.toMatrix b b).symm_apply_apply N
    rw [LinearMap.toMatrix_symm] at this
    conv_lhs => rw [← this]
    rw [Matrix.toLin_self]
  have hu : ∀ i, IsUnit (M i i) := fun i => by
    have h := hN i i
    simp only [Matrix.one_apply_eq] at h
    by_contra hnu
    have : (1 : R) ∈ maximalIdeal R := by
      have h2 : M i i ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      have := Ideal.sub_mem _ h2 h
      rwa [sub_sub_cancel] at this
    exact (Ideal.ne_top_iff_one _).mp (Ideal.IsMaximal.ne_top inferInstance) this
  refine ⟨M 0 0, M 1 1, hu 0, hu 1, ?_, ?_⟩
  · rw [hNb 0, Fin.sum_univ_two, h10, zero_smul, add_zero]
  · rw [hNb 1, Fin.sum_univ_two, h01, zero_smul, zero_add]

end S_LinearMap_exists_apply_basis_eq_smul_of_mul_eq_pow_mul_of_toMatrix_sub_one_mem
end P2MW
export P2MW.S_LinearMap_exists_apply_basis_eq_smul_of_mul_eq_pow_mul_of_toMatrix_sub_one_mem (solution)
