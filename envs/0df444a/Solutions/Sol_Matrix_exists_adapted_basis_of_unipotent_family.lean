-- Prove2me | solution 1 for Matrix.exists_adapted_basis_of_unipotent_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c3ddd79f-ce8e-5580-9af9-0ae1611e1d23

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Valuation.ValuationRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_exists_adapted_basis_of_unipotent_family

set_option autoImplicit false

private def sl2M {R : Type} [CommRing R] (s t u : R) : Matrix (Fin 2) (Fin 2) R :=
  Matrix.of ![![s, t], ![u, -s]]

section Helpers

variable {R : Type} [CommRing R]

private theorem trace_eq_zero_of_mul_self_eq_zero [NoZeroDivisors R]
    (N : Matrix (Fin 2) (Fin 2) R) (hN : N * N = 0) : N.trace = 0 := by
  have h00 : N 0 0 * N 0 0 + N 0 1 * N 1 0 = 0 := by
    have := congrFun (congrFun hN 0) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : N 0 0 * N 0 1 + N 0 1 * N 1 1 = 0 := by
    have := congrFun (congrFun hN 0) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : N 1 0 * N 0 0 + N 1 1 * N 1 0 = 0 := by
    have := congrFun (congrFun hN 1) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : N 1 0 * N 0 1 + N 1 1 * N 1 1 = 0 := by
    have := congrFun (congrFun hN 1) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  rw [Matrix.trace_fin_two]
  by_contra h
  have hb : N 0 1 = 0 := by
    have : N 0 1 * (N 0 0 + N 1 1) = 0 := by rw [← h01]; ring
    exact (mul_eq_zero.mp this).resolve_right h
  have hc : N 1 0 = 0 := by
    have : N 1 0 * (N 0 0 + N 1 1) = 0 := by rw [← h10]; ring
    exact (mul_eq_zero.mp this).resolve_right h
  have ha : N 0 0 = 0 := by
    have : N 0 0 * N 0 0 = 0 := by rw [← h00, hb]; ring
    exact (mul_self_eq_zero.mp this)
  have hd : N 1 1 = 0 := by
    have : N 1 1 * N 1 1 = 0 := by rw [← h11, hc]; ring
    exact (mul_self_eq_zero.mp this)
  exact h (by rw [ha, hd, add_zero])

private theorem eq_line_of_unipotent_mul [NoZeroDivisors R] (t : R) (ht : t ≠ 0)
    (N : Matrix (Fin 2) (Fin 2) R) (hN : N * N = 0)
    (hu : ((1 + sl2M 0 t 0) * (1 + N)).trace = 2) : N = sl2M 0 (N 0 1) 0 := by
  have htrN : N 0 0 + N 1 1 = 0 := by
    rw [← Matrix.trace_fin_two]; exact trace_eq_zero_of_mul_self_eq_zero N hN
  have htr : ((1 + sl2M 0 t 0) * (1 + N)).trace = 2 + (N 0 0 + N 1 1) + t * N 1 0 := by
    simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, sl2M, Matrix.one_apply]
    ring
  have hc : N 1 0 = 0 := by
    have : t * N 1 0 = 0 := by
      have h2 := hu; rw [htr, htrN, add_zero] at h2
      simpa using h2
    exact (mul_eq_zero.mp this).resolve_left ht
  have h00 : N 0 0 * N 0 0 + N 0 1 * N 1 0 = 0 := by
    have := congrFun (congrFun hN 0) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have ha : N 0 0 = 0 := by
    have : N 0 0 * N 0 0 = 0 := by rw [← h00, hc]; ring
    exact mul_self_eq_zero.mp this
  have hd : N 1 1 = 0 := by rw [ha, zero_add] at htrN; exact htrN
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2M, ha, hc, hd]

private theorem exists_conj_eq_line [IsDomain R] [ValuationRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (hM : M * M = 0) (hM0 : M ≠ 0) :
    ∃ P : Matrix (Fin 2) (Fin 2) R, IsUnit P.det ∧ ∃ t : R, t ≠ 0 ∧ M * P = P * sl2M 0 t 0 := by
  have htr : M 0 0 + M 1 1 = 0 := by
    rw [← Matrix.trace_fin_two]; exact trace_eq_zero_of_mul_self_eq_zero M hM
  have hd : M 1 1 = -M 0 0 := by rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact htr
  have h00 : M 0 0 * M 0 0 + M 0 1 * M 1 0 = 0 := by
    have := congrFun (congrFun hM 0) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hMe : M = Matrix.of ![![M 0 0, M 0 1], ![M 1 0, -M 0 0]] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hd]
  rcases ValuationRing.dvd_total (M 0 1) (M 0 0) with ⟨l, hl⟩ | ⟨m, hm⟩
  · by_cases hb : M 0 1 = 0
    · have ha : M 0 0 = 0 := by rw [hl, hb, zero_mul]
      have hc : M 1 0 ≠ 0 := by
        intro hc; apply hM0; rw [hMe]; ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc]
      refine ⟨Matrix.of ![![0, 1], ![1, 0]], ?_, M 1 0, hc, ?_⟩
      · simp [Matrix.det_fin_two]
      · rw [hMe]; ext i j
        fin_cases i <;> fin_cases j <;> simp [sl2M, Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
    · have hc : M 1 0 = -(l * l * M 0 1) := by
        have : M 0 1 * (M 1 0 + l * l * M 0 1) = 0 := by rw [← h00, hl]; ring
        have h2 := (mul_eq_zero.mp this).resolve_left hb
        exact eq_neg_of_add_eq_zero_left h2
      refine ⟨Matrix.of ![![1, 0], ![-l, 1]], ?_, M 0 1, hb, ?_⟩
      · simp [Matrix.det_fin_two]
      · rw [hMe]; ext i j
        fin_cases i <;> fin_cases j <;>
          simp [sl2M, Matrix.mul_apply, Fin.sum_univ_two, hl, hc] <;> ring
  · by_cases ha : M 0 0 = 0
    · have hb : M 0 1 = 0 := by rw [hm, ha, zero_mul]
      have hc : M 1 0 ≠ 0 := by
        intro hc; apply hM0; rw [hMe]; ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc]
      refine ⟨Matrix.of ![![0, 1], ![1, 0]], ?_, M 1 0, hc, ?_⟩
      · simp [Matrix.det_fin_two]
      · rw [hMe]; ext i j
        fin_cases i <;> fin_cases j <;> simp [sl2M, Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
    · have hac : M 0 0 = -(m * M 1 0) := by
        have : M 0 0 * (M 0 0 + m * M 1 0) = 0 := by rw [← h00, hm]; ring
        have h2 := (mul_eq_zero.mp this).resolve_left ha
        exact eq_neg_of_add_eq_zero_left h2
      have hc : M 1 0 ≠ 0 := by intro hc; apply ha; rw [hac, hc, mul_zero, neg_zero]
      refine ⟨Matrix.of ![![-m, 1], ![1, 0]], ?_, M 1 0, hc, ?_⟩
      · simp [Matrix.det_fin_two]
      · rw [hMe]; ext i j
        fin_cases i <;> fin_cases j <;>
          simp [sl2M, Matrix.mul_apply, Fin.sum_univ_two, hm, hac]
        all_goals ring

private theorem one_add_line (s : R) :
    (1 : Matrix (Fin 2) (Fin 2) R) + sl2M 0 s 0 = Matrix.of ![![1, s], ![0, 1]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2M]

end Helpers

theorem solution {R : Type} [CommRing R] [IsDomain R]
    [ValuationRing R] (T : Set (Matrix (Fin 2) (Fin 2) R))
    (hmul : ∀ A ∈ T, ∀ B ∈ T, A * B ∈ T)
    (hsq : ∀ A ∈ T, (A - 1) * (A - 1) = 0)
    (A₀ : Matrix (Fin 2) (Fin 2) R) (hA₀ : A₀ ∈ T) (hA₀ne : A₀ ≠ 1) :
    ∃ P : Matrix (Fin 2) (Fin 2) R, IsUnit P.det ∧
      (∃ t : R, t ≠ 0 ∧ A₀ * P = P * Matrix.of ![![1, t], ![0, 1]]) ∧
      ∀ A ∈ T, ∃ s : R, A * P = P * Matrix.of ![![1, s], ![0, 1]] := by
  classical
  have hN₀sq : (A₀ - 1) * (A₀ - 1) = 0 := hsq A₀ hA₀
  have hN₀ne : A₀ - 1 ≠ 0 := fun hz => hA₀ne (by rwa [sub_eq_zero] at hz)
  obtain ⟨P, hPdet, t, ht, hNP⟩ := exists_conj_eq_line (A₀ - 1) hN₀sq hN₀ne
  haveI := P.invertibleOfIsUnitDet hPdet
  have h2tr : ∀ B ∈ T, B.trace = 2 := by
    intro B hB
    have h0 := trace_eq_zero_of_mul_self_eq_zero (B - 1) (hsq B hB)
    rw [Matrix.trace_sub, Matrix.trace_one, sub_eq_zero] at h0
    simpa [Fintype.card_fin] using h0
  have htrconj : ∀ X : Matrix (Fin 2) (Fin 2) R, (⅟P * X * P).trace = X.trace := by
    intro X
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]
  have h1ptE : ⅟P * A₀ * P = 1 + sl2M 0 t 0 := by
    have key : ⅟P * (A₀ - 1) * P = ⅟P * A₀ * P - 1 := by
      rw [mul_sub, mul_one, sub_mul, invOf_mul_self]
    have hconj : ⅟P * (A₀ - 1) * P = sl2M 0 t 0 := by
      rw [Matrix.mul_assoc, hNP, ← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul]
    rw [key] at hconj
    rw [← hconj]; abel
  have hA₀P : A₀ * P = P * (1 + sl2M 0 t 0) := by
    rw [← h1ptE, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]
  refine ⟨P, hPdet, ⟨t, ht, by rw [hA₀P, one_add_line]⟩, ?_⟩
  intro A hA
  have key : ⅟P * (A - 1) * P = ⅟P * A * P - 1 := by
    rw [mul_sub, mul_one, sub_mul, invOf_mul_self]
  have hÑsq : (⅟P * (A - 1) * P) * (⅟P * (A - 1) * P) = 0 := by
    have hshuffle : (⅟P * (A - 1) * P) * (⅟P * (A - 1) * P)
        = ⅟P * ((A - 1) * (A - 1)) * P := by
      calc (⅟P * (A - 1) * P) * (⅟P * (A - 1) * P)
          = ⅟P * (A - 1) * (P * (⅟P * ((A - 1) * P))) := by
            simp only [Matrix.mul_assoc]
        _ = ⅟P * (A - 1) * ((P * ⅟P) * ((A - 1) * P)) := by rw [← Matrix.mul_assoc P]
        _ = ⅟P * ((A - 1) * (A - 1)) * P := by
            rw [mul_invOf_self, Matrix.one_mul]; simp only [Matrix.mul_assoc]
    rw [hshuffle, hsq A hA, Matrix.mul_zero, Matrix.zero_mul]
  have hu : ((1 + sl2M 0 t 0) * (1 + (⅟P * (A - 1) * P))).trace = 2 := by
    have h1pÑ : 1 + (⅟P * (A - 1) * P) = ⅟P * A * P := by rw [key]; abel
    have hprod : (⅟P * A₀ * P) * (⅟P * A * P) = ⅟P * (A₀ * A) * P := by
      calc (⅟P * A₀ * P) * (⅟P * A * P)
          = ⅟P * A₀ * (P * (⅟P * (A * P))) := by simp only [Matrix.mul_assoc]
        _ = ⅟P * A₀ * ((P * ⅟P) * (A * P)) := by rw [← Matrix.mul_assoc P]
        _ = ⅟P * (A₀ * A) * P := by
            rw [mul_invOf_self, Matrix.one_mul]; simp only [Matrix.mul_assoc]
    rw [← h1ptE, h1pÑ, hprod, htrconj]
    exact h2tr _ (hmul A₀ hA₀ A hA)
  have hline := eq_line_of_unipotent_mul t ht (⅟P * (A - 1) * P) hÑsq hu
  refine ⟨(⅟P * (A - 1) * P) 0 1, ?_⟩
  have h1pÑ : 1 + (⅟P * (A - 1) * P) = ⅟P * A * P := by rw [key]; abel
  have hPA : P * (1 + (⅟P * (A - 1) * P)) = A * P := by
    rw [h1pÑ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]
  rw [← one_add_line, ← hPA]
  exact congrArg (fun X => P * (1 + X)) hline

end S_Matrix_exists_adapted_basis_of_unipotent_family
end P2MW
export P2MW.S_Matrix_exists_adapted_basis_of_unipotent_family (solution)
