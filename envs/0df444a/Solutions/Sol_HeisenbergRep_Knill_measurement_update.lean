-- Prove2me | solution 1 for HeisenbergRep.Knill.measurement_update
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:52:50.900501+00:00
-- url     : https://prove2.me/submissions/01242f16-c942-489a-8bca-e529dd063e2f

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QECC

namespace Aux_HeisenbergRep_Knill_measurement_update

open QAlgorithms QAlgorithms.Stabilizer
open scoped Matrix

section act_lemmas

variable {ι : Type*} [Fintype ι]

lemma act_mul (A B : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (A * B) v = act A (act B v) := by
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec_mulVec]

lemma act_add (A B : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (A + B) v = act A v + act B v := by
  simp only [act, Matrix.add_mulVec, WithLp.toLp_add]

lemma act_smul (c : ℂ) (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (c • A) v = c • act A v := by
  simp only [act, Matrix.smul_mulVec, WithLp.toLp_smul]

lemma act_one [DecidableEq ι] (v : EuclideanSpace ℂ ι) : act (1 : Matrix ι ι ℂ) v = v := by
  simp only [act, Matrix.one_mulVec, WithLp.toLp_ofLp]

lemma act_neg (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) : act (-A) v = -act A v := by
  simp only [act, Matrix.neg_mulVec, WithLp.toLp_neg]

lemma act_vadd (A : Matrix ι ι ℂ) (v w : EuclideanSpace ℂ ι) :
    act A (v + w) = act A v + act A w := by
  simp only [act, WithLp.ofLp_add, Matrix.mulVec_add, WithLp.toLp_add]

lemma act_vsub (A : Matrix ι ι ℂ) (v w : EuclideanSpace ℂ ι) :
    act A (v - w) = act A v - act A w := by
  simp only [act, WithLp.ofLp_sub, Matrix.mulVec_sub, WithLp.toLp_sub]

lemma act_vneg (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) : act A (-v) = -act A v := by
  simp only [act, WithLp.ofLp_neg, Matrix.mulVec_neg, WithLp.toLp_neg]

lemma act_vsmul (A : Matrix ι ι ℂ) (c : ℂ) (v : EuclideanSpace ℂ ι) :
    act A (c • v) = c • act A v := by
  simp only [act, WithLp.ofLp_smul, Matrix.mulVec_smul, WithLp.toLp_smul]

lemma act_vzero (A : Matrix ι ι ℂ) : act A (0 : EuclideanSpace ℂ ι) = 0 := by
  simp only [act, WithLp.ofLp_zero, Matrix.mulVec_zero, WithLp.toLp_zero]

end act_lemmas

lemma my_eq_zero_of_neg_eq {E : Type*} [AddCommGroup E] [Module ℂ E] [NoZeroSMulDivisors ℂ E]
    (v : E) (h : -v = v) : v = 0 := by
  have h2 : (2 : ℂ) • v = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h]
    exact neg_add_cancel v
  rcases smul_eq_zero.mp h2 with h3 | h3
  · norm_num at h3
  · exact h3

lemma pauli_sq (P : Pauli) : P.mat * P.mat = 1 := by
  cases P <;> ext a b <;> cases a <;> cases b <;>
    simp [Pauli.mat, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fintype.sum_bool,
      Matrix.one_apply, Matrix.diagonal_apply]

lemma toMatrix_sq {n : ℕ} (A₀ : PauliString n) (h : A₀.phase = 0 ∨ A₀.phase = 2) :
    A₀.toMatrix * A₀.toMatrix = 1 := by
  have hph : Complex.I ^ A₀.phase.val * Complex.I ^ A₀.phase.val = 1 := by
    rcases h with h | h
    · rw [h, ZMod.val_zero, pow_zero, one_mul]
    · rw [h]
      have h2 : (2 : ZMod 4).val = 2 := rfl
      rw [h2, Complex.I_sq]
      norm_num
  ext y z
  rw [Matrix.mul_apply]
  simp only [PauliString.toMatrix, Matrix.of_apply]
  have step1 : ∑ w : Qubits n, (Complex.I ^ A₀.phase.val * ∏ q, (A₀.ops q).mat (y q) (w q)) *
      (Complex.I ^ A₀.phase.val * ∏ q, (A₀.ops q).mat (w q) (z q)) =
      ∏ q, ∑ b : Bool, (A₀.ops q).mat (y q) b * (A₀.ops q).mat b (z q) := by
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.prod_mul_distrib]
    linear_combination (∏ q, (A₀.ops q).mat (y q) (w q)) * (∏ q, (A₀.ops q).mat (w q) (z q)) * hph
  rw [step1]
  have step2 : ∀ q : Fin n, ∑ b : Bool, (A₀.ops q).mat (y q) b * (A₀.ops q).mat b (z q) =
      if y q = z q then 1 else 0 := by
    intro q
    rw [← Matrix.mul_apply, pauli_sq, Matrix.one_apply]
  simp only [step2]
  rw [Fintype.prod_boole, Matrix.one_apply]
  by_cases hyz : y = z
  · rw [if_pos (show ∀ q, y q = z q from fun q => by rw [hyz]), if_pos hyz]
  · rw [if_neg (show ¬ ∀ q, y q = z q from fun h => hyz (funext h)), if_neg hyz]

end Aux_HeisenbergRep_Knill_measurement_update

open Aux_HeisenbergRep_Knill_measurement_update in
open QAlgorithms QAlgorithms.Stabilizer in
open scoped Matrix in
theorem solution {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) (hψ : ψ ≠ 0)
    (S : Set (Matrix.unitaryGroup (Qubits n) ℂ)) (hSP : S ⊆ pauliGroup n)
    (hSψ : ∀ N ∈ S, act (N : Matrix (Qubits n) (Qubits n) ℂ) ψ = ψ)
    (A₀ : PauliString n) (hA₀ : A₀.phase = 0 ∨ A₀.phase = 2)
    (M : Matrix.unitaryGroup (Qubits n) ℂ) (hMS : M ∈ S)
    (hMA : (M : Matrix (Qubits n) (Qubits n) ℂ) * A₀.toMatrix =
      -(A₀.toMatrix * (M : Matrix (Qubits n) (Qubits n) ℂ))) :
    let ψ' := act ((2⁻¹ : ℂ) • (1 + A₀.toMatrix)) ψ
    ψ' ≠ 0 ∧
    act A₀.toMatrix ψ' = ψ' ∧
    act (M : Matrix (Qubits n) (Qubits n) ℂ) ψ' ≠ ψ' ∧
    (∀ N ∈ S, (N : Matrix (Qubits n) (Qubits n) ℂ) * A₀.toMatrix =
        A₀.toMatrix * (N : Matrix (Qubits n) (Qubits n) ℂ) →
      act (N : Matrix (Qubits n) (Qubits n) ℂ) ψ' = ψ') ∧
    (∀ N ∈ S, (N : Matrix (Qubits n) (Qubits n) ℂ) * A₀.toMatrix =
        -(A₀.toMatrix * (N : Matrix (Qubits n) (Qubits n) ℂ)) →
      act (N : Matrix (Qubits n) (Qubits n) ℂ) ψ' ≠ ψ' ∧
      act ((M * N : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ) ψ' = ψ' ∧
      ((M * N : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ) * A₀.toMatrix =
        A₀.toMatrix * ((M * N : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ)) ∧
    (∀ L ∈ pauliGroup n, (∀ N ∈ S, L * N = N * L) →
      (L : Matrix (Qubits n) (Qubits n) ℂ) * A₀.toMatrix =
        -(A₀.toMatrix * (L : Matrix (Qubits n) (Qubits n) ℂ)) →
      ((M * L : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ) * A₀.toMatrix =
          A₀.toMatrix * ((M * L : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ) ∧
        ∀ φ : EuclideanSpace ℂ (Qubits n),
          (∀ N ∈ S, act (N : Matrix (Qubits n) (Qubits n) ℂ) φ = φ) →
          act ((M * L : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ) φ =
            act (L : Matrix (Qubits n) (Qubits n) ℂ) φ) := by
  intro ψ'
  have hψ' : ψ' = act ((2⁻¹ : ℂ) • (1 + A₀.toMatrix)) ψ := rfl
  clear_value ψ'
  have hA2 : A₀.toMatrix * A₀.toMatrix = 1 := toMatrix_sq A₀ hA₀
  have hMψ : act (M : Matrix (Qubits n) (Qubits n) ℂ) ψ = ψ := hSψ M hMS
  have hψ'v : ψ' = (2⁻¹ : ℂ) • (ψ + act A₀.toMatrix ψ) := by
    rw [hψ', act_smul, act_add, act_one]
  have hAA : ψ = act A₀.toMatrix (act A₀.toMatrix ψ) := by
    rw [← act_mul, hA2, act_one]
  -- anticommuting elements fixing ψ
  have anti : ∀ N : Matrix (Qubits n) (Qubits n) ℂ, N * A₀.toMatrix = -(A₀.toMatrix * N) →
      act N ψ = ψ → act N ψ' = (2⁻¹ : ℂ) • (ψ - act A₀.toMatrix ψ) := by
    intro N hN hNψ
    rw [hψ'v, act_vsmul, act_vadd, hNψ, ← act_mul, hN, act_neg, act_mul, hNψ, sub_eq_add_neg]
  have noteq : ∀ N : Matrix (Qubits n) (Qubits n) ℂ, N * A₀.toMatrix = -(A₀.toMatrix * N) →
      act N ψ = ψ → act N ψ' ≠ ψ' := by
    intro N hN hNψ heq
    rw [anti N hN hNψ, hψ'v] at heq
    have h1 := smul_right_injective (EuclideanSpace ℂ (Qubits n))
      (inv_ne_zero (by norm_num : (2 : ℂ) ≠ 0)) heq
    have h2 : act A₀.toMatrix ψ = 0 := by
      apply my_eq_zero_of_neg_eq
      have h3 : ψ + -(act A₀.toMatrix ψ) = ψ + act A₀.toMatrix ψ := by
        rw [← sub_eq_add_neg]
        exact h1
      exact add_left_cancel h3
    apply hψ
    rw [hAA, h2, act_vzero]
  have comm : ∀ N : Matrix (Qubits n) (Qubits n) ℂ, N * A₀.toMatrix = A₀.toMatrix * N →
      act N ψ = ψ → act N ψ' = ψ' := by
    intro N hN hNψ
    rw [hψ'v, act_vsmul, act_vadd, hNψ, ← act_mul, hN, act_mul, hNψ]
  have commMul : ∀ L : Matrix (Qubits n) (Qubits n) ℂ, L * A₀.toMatrix = -(A₀.toMatrix * L) →
      (M : Matrix (Qubits n) (Qubits n) ℂ) * L * A₀.toMatrix =
        A₀.toMatrix * ((M : Matrix (Qubits n) (Qubits n) ℂ) * L) := by
    intro L hL
    calc (M : Matrix (Qubits n) (Qubits n) ℂ) * L * A₀.toMatrix
        = (M : Matrix (Qubits n) (Qubits n) ℂ) * (L * A₀.toMatrix) := mul_assoc _ _ _
      _ = (M : Matrix (Qubits n) (Qubits n) ℂ) * (-(A₀.toMatrix * L)) := by rw [hL]
      _ = -((M : Matrix (Qubits n) (Qubits n) ℂ) * A₀.toMatrix * L) := by
          rw [mul_neg, mul_assoc]
      _ = -(-(A₀.toMatrix * (M : Matrix (Qubits n) (Qubits n) ℂ)) * L) := by rw [hMA]
      _ = A₀.toMatrix * ((M : Matrix (Qubits n) (Qubits n) ℂ) * L) := by
          rw [neg_mul, neg_neg, mul_assoc]
  refine ⟨?_, ?_, noteq _ hMA hMψ, fun N hN hNA => comm _ hNA (hSψ N hN), ?_, ?_⟩
  · -- ψ' ≠ 0
    intro h0
    rw [hψ'v] at h0
    have h1 : ψ + act A₀.toMatrix ψ = 0 := by
      rcases smul_eq_zero.mp h0 with h | h
      · norm_num at h
      · exact h
    have haψ : act A₀.toMatrix ψ = -ψ := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact h1
    have e1 : act ((M : Matrix (Qubits n) (Qubits n) ℂ) * A₀.toMatrix) ψ = -ψ := by
      rw [act_mul, haψ, act_vneg, hMψ]
    have e2 : act (-(A₀.toMatrix * (M : Matrix (Qubits n) (Qubits n) ℂ))) ψ = ψ := by
      rw [act_neg, act_mul, hMψ, haψ, neg_neg]
    rw [hMA, e2] at e1
    exact hψ (my_eq_zero_of_neg_eq ψ e1.symm)
  · -- A ψ' = ψ'
    rw [hψ'v, act_vsmul, act_vadd, ← hAA, add_comm]
  · -- anticommuting N
    intro N hN hNA
    have hNψ := hSψ N hN
    refine ⟨noteq _ hNA hNψ, ?_, commMul _ hNA⟩
    show act ((M : Matrix (Qubits n) (Qubits n) ℂ) * (N : Matrix (Qubits n) (Qubits n) ℂ)) ψ' = ψ'
    rw [act_mul, anti _ hNA hNψ, act_vsmul, act_vsub, hMψ, ← act_mul, hMA, act_neg, act_mul,
      hMψ, sub_neg_eq_add, hψ'v]
  · -- logical operators
    intro L _ hLS hLA
    refine ⟨commMul _ hLA, ?_⟩
    intro φ hφ
    have hLM : (L : Matrix (Qubits n) (Qubits n) ℂ) * (M : Matrix (Qubits n) (Qubits n) ℂ) =
        (M : Matrix (Qubits n) (Qubits n) ℂ) * (L : Matrix (Qubits n) (Qubits n) ℂ) :=
      congrArg (fun U : Matrix.unitaryGroup (Qubits n) ℂ => (U : Matrix (Qubits n) (Qubits n) ℂ))
        (hLS M hMS)
    show act ((M : Matrix (Qubits n) (Qubits n) ℂ) * (L : Matrix (Qubits n) (Qubits n) ℂ)) φ =
      act (L : Matrix (Qubits n) (Qubits n) ℂ) φ
    rw [← hLM, act_mul, hφ M hMS]
