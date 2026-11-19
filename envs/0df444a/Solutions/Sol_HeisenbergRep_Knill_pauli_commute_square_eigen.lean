-- Prove2me | solution 1 for HeisenbergRep.Knill.pauli_commute_square_eigen
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T03:44:54.578629+00:00
-- url     : https://prove2.me/submissions/75f681e3-16ee-43f8-82d0-f716443ff4a4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Stabilizer

open QAlgorithms QAlgorithms.Stabilizer
open scoped Matrix

private def pauliAnticomm : Pauli → Pauli → Bool
  | .I, _ => false
  | _, .I => false
  | .X, .X => false
  | .Y, .Y => false
  | .Z, .Z => false
  | _, _ => true

private lemma pauli_mat_mul_comm (p q : Pauli) :
    p.mat * q.mat = (if pauliAnticomm p q then (-1 : ℂ) else 1) • (q.mat * p.mat) := by
  cases p <;> cases q <;> ext i j <;> cases i <;> cases j <;>
    simp [Pauli.mat, pauliAnticomm, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fintype.sum_bool] <;>
    ring

private lemma pauli_mat_sq (p : Pauli) : p.mat * p.mat = 1 := by
  cases p <;> ext i j <;> cases i <;> cases j <;>
    simp [Pauli.mat, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fintype.sum_bool]

private lemma toMatrix_mul_apply {n : ℕ} (P Q : PauliString n) (x z : Qubits n) :
    (P.toMatrix * Q.toMatrix) x z =
      Complex.I ^ (P.phase.val + Q.phase.val) *
        ∏ q : Fin n, ((P.ops q).mat * (Q.ops q).mat) (x q) (z q) := by
  simp only [PauliString.toMatrix, Matrix.mul_apply, Matrix.of_apply]
  have hterm : ∀ y : Qubits n,
      (Complex.I ^ P.phase.val * ∏ q : Fin n, (P.ops q).mat (x q) (y q)) *
        (Complex.I ^ Q.phase.val * ∏ q : Fin n, (Q.ops q).mat (y q) (z q)) =
      Complex.I ^ (P.phase.val + Q.phase.val) *
        ∏ q : Fin n, ((P.ops q).mat (x q) (y q) * (Q.ops q).mat (y q) (z q)) := by
    intro y
    rw [mul_mul_mul_comm, ← pow_add, ← Finset.prod_mul_distrib]
  simp_rw [hterm, ← Finset.mul_sum]
  congr 1
  symm
  exact Fintype.prod_sum fun q b => (P.ops q).mat (x q) b * (Q.ops q).mat b (z q)

theorem solution {n : ℕ} (P Q : PauliString n) :
    (P.toMatrix * Q.toMatrix = Q.toMatrix * P.toMatrix ∨
      P.toMatrix * Q.toMatrix = -(Q.toMatrix * P.toMatrix)) ∧
    ((P.phase = 0 ∨ P.phase = 2) → P.toMatrix ^ 2 = 1) ∧
    ((P.phase = 1 ∨ P.phase = 3) → P.toMatrix ^ 2 = -1) ∧
    ∀ (v : Qubits n → ℂ) (μ : ℂ), v ≠ 0 → P.toMatrix *ᵥ v = μ • v →
      ((P.phase = 0 ∨ P.phase = 2) → μ = 1 ∨ μ = -1) ∧
      ((P.phase = 1 ∨ P.phase = 3) → μ = Complex.I ∨ μ = -Complex.I) := by
  have hsq_eq : P.toMatrix ^ 2 = (Complex.I ^ (2 * P.phase.val)) • (1 : Matrix (Qubits n) (Qubits n) ℂ) := by
    rw [sq]
    ext x z
    rw [toMatrix_mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    have hprod : (∏ q : Fin n, ((P.ops q).mat * (P.ops q).mat) (x q) (z q)) =
        if x = z then 1 else 0 := by
      simp_rw [pauli_mat_sq, Matrix.one_apply]
      by_cases h : x = z
      · subst h; simp
      · simp only [if_neg h]
        obtain ⟨q, hq⟩ : ∃ q : Fin n, x q ≠ z q := by
          by_contra hall
          push Not at hall
          exact h (funext hall)
        exact Finset.prod_eq_zero (Finset.mem_univ q) (if_neg hq)
    rw [hprod, two_mul]
  have hsq02 : (P.phase = 0 ∨ P.phase = 2) → P.toMatrix ^ 2 = 1 := by
    intro hp
    rw [hsq_eq]
    rcases hp with h0 | h2
    · have hv : P.phase.val = 0 := by rw [h0]; rfl
      simp [hv]
    · have hv : P.phase.val = 2 := by rw [h2]; rfl
      rw [hv]
      have hi : Complex.I ^ (2 * 2) = 1 := by norm_num [pow_succ, Complex.I_sq]
      rw [hi, one_smul]
  have hsq13 : (P.phase = 1 ∨ P.phase = 3) → P.toMatrix ^ 2 = -1 := by
    intro hp
    rw [hsq_eq]
    rcases hp with h1 | h3
    · have hv : P.phase.val = 1 := by rw [h1]; rfl
      rw [hv]
      have hi : Complex.I ^ (2 * 1) = -1 := by simp [Complex.I_sq]
      rw [hi, neg_one_smul]
    · have hv : P.phase.val = 3 := by rw [h3]; rfl
      rw [hv]
      have hi : Complex.I ^ (2 * 3) = -1 := by
        calc Complex.I ^ (2 * 3) = (Complex.I ^ 2) ^ 3 := by ring
          _ = (-1) ^ 3 := by rw [Complex.I_sq]
          _ = -1 := by norm_num
      rw [hi, neg_one_smul]
  refine ⟨?_, hsq02, hsq13, ?_⟩
  · let k : ℕ := (Finset.univ.filter fun q : Fin n => pauliAnticomm (P.ops q) (Q.ops q) = true).card
    have hcomm : P.toMatrix * Q.toMatrix = ((-1 : ℂ) ^ k) • (Q.toMatrix * P.toMatrix) := by
      ext x z
      rw [toMatrix_mul_apply, Matrix.smul_apply, toMatrix_mul_apply, smul_eq_mul]
      have hprod : (∏ q : Fin n, ((P.ops q).mat * (Q.ops q).mat) (x q) (z q)) =
          (-1 : ℂ) ^ k * ∏ q : Fin n, ((Q.ops q).mat * (P.ops q).mat) (x q) (z q) := by
        have hpt : ∀ q : Fin n, ((P.ops q).mat * (Q.ops q).mat) (x q) (z q) =
            (if pauliAnticomm (P.ops q) (Q.ops q) then (-1 : ℂ) else 1) *
              ((Q.ops q).mat * (P.ops q).mat) (x q) (z q) := by
          intro q
          rw [pauli_mat_mul_comm (P.ops q) (Q.ops q), Matrix.smul_apply, smul_eq_mul]
        simp_rw [hpt, Finset.prod_mul_distrib]
        congr 1
        simp [k, Finset.prod_ite, Finset.prod_const_one, mul_one]
      rw [hprod, add_comm P.phase.val Q.phase.val]
      ring
    rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · left; rw [hcomm, hm, ← two_mul, pow_mul]; norm_num
    · right; rw [hcomm, hm, pow_add, pow_mul]; norm_num
  · intro v μ hv hmul
    have hv2 : (P.toMatrix ^ 2) *ᵥ v = (μ ^ 2) • v := by
      rw [sq, ← Matrix.mulVec_mulVec, hmul, Matrix.mulVec_smul, hmul, smul_smul, sq]
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · rw [hsq02 hp, Matrix.one_mulVec] at hv2
      have hdiff : (μ ^ 2 - 1) • v = 0 := by
        rw [sub_smul, one_smul, ← hv2, sub_self]
      rcases smul_eq_zero.mp hdiff with hμ | hv0
      · have hfac : (μ - 1) * (μ + 1) = 0 := by linear_combination hμ
        rcases mul_eq_zero.mp hfac with h1 | h2
        · left; exact sub_eq_zero.mp h1
        · right; exact eq_neg_of_add_eq_zero_left h2
      · exact absurd hv0 hv
    · rw [hsq13 hp, Matrix.neg_mulVec, Matrix.one_mulVec] at hv2
      have hdiff : (μ ^ 2 + 1) • v = 0 := by
        rw [add_smul, one_smul, ← hv2, neg_add_cancel]
      rcases smul_eq_zero.mp hdiff with hμ | hv0
      · have hfac : (μ - Complex.I) * (μ + Complex.I) = 0 := by
          linear_combination hμ - Complex.I_sq
        rcases mul_eq_zero.mp hfac with h1 | h2
        · left; exact sub_eq_zero.mp h1
        · right; exact eq_neg_of_add_eq_zero_left h2
      · exact absurd hv0 hv
