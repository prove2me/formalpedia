-- Prove2me | solution 1 for LindbladStructLearn.lemma_2_7
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T22:33:43.079143+00:00
-- url     : https://prove2.me/submissions/384ad5e8-41b6-474e-a736-966f55c7a0d8

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_LindbladStructLearn_pauliAvg
import Definitions.Def_LindbladStructLearn_chi
import Definitions.Def_LindbladStructLearn_ntr
import Definitions.Def_LindbladStructLearn_restrict
import Definitions.Def_LindbladStructLearn_pairSupport

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn.FourierAux
open LindbladTolerant.Testing LindbladStructLearn

/-- tensor product of single-qubit matrices -/
def tens {n : ℕ} (a : Fin n → Op Bool) : Op (Qubits n) := fun x y => ∏ i, a i (x i) (y i)

lemma tens_mul {n : ℕ} (a b : Fin n → Op Bool) :
    tens a * tens b = tens (fun i => a i * b i) := by
  ext x z
  simp only [tens, Matrix.mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp [Finset.prod_mul_distrib]

lemma tens_conjTranspose {n : ℕ} (a : Fin n → Op Bool) :
    (tens a)ᴴ = tens (fun i => (a i)ᴴ) := by
  ext x y
  simp [tens, Matrix.conjTranspose_apply]

lemma tens_trace {n : ℕ} (a : Fin n → Op Bool) :
    (tens a).trace = ∏ i, (a i).trace := by
  simp only [Matrix.trace, Matrix.diag, tens]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

lemma ntr_tens {n : ℕ} (a : Fin n → Op Bool) :
    ntr (tens a) = ∏ i, (a i).trace / 2 := by
  rw [ntr, tens_trace, Finset.prod_div_distrib]
  simp

lemma pauliMatrix_eq_tens {n : ℕ} (p : Pauli n) :
    pauliMatrix p = tens (fun i => onePauli (p i)) := rfl

lemma onePauli_conjTranspose (a : Fin 4) : (onePauli a)ᴴ = onePauli a := by
  ext x y
  fin_cases a <;> cases x <;> cases y <;> simp [onePauli, Matrix.conjTranspose_apply]

lemma onePauli_zero : onePauli 0 = 1 := by
  ext x y; cases x <;> cases y <;> simp [onePauli]

lemma trace_onePauli_mul (a c : Fin 4) :
    (onePauli a * onePauli c).trace = if a = c then 2 else 0 := by
  fin_cases a <;> fin_cases c <;>
    simp [onePauli, Matrix.trace, Matrix.mul_apply] <;> norm_num

lemma twirl (M : Op Bool) :
    ∑ r : Fin 4, onePauli r * M * onePauli r = (2 * M.trace) • (1 : Op Bool) := by
  ext x y
  simp only [Fin.sum_univ_four, Matrix.add_apply]
  cases x <;> cases y <;>
    simp [onePauli, Matrix.mul_apply, Matrix.trace] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

lemma single_avg (a b c d : Fin 4) :
    (∑ r : Fin 4, ((onePauli a * onePauli r * onePauli b)ᴴ *
        (onePauli c * onePauli r * onePauli d)).trace / 2) / 4 =
      if a = c ∧ b = d then 1 else 0 := by
  have key : ∀ r : Fin 4, ((onePauli a * onePauli r * onePauli b)ᴴ *
        (onePauli c * onePauli r * onePauli d)).trace =
      (onePauli r * (onePauli a * onePauli c) * onePauli r * (onePauli d * onePauli b)).trace := by
    intro r
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, onePauli_conjTranspose,
      onePauli_conjTranspose, onePauli_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm (onePauli b)]
    simp only [Matrix.mul_assoc]
  simp_rw [key]
  rw [← Finset.sum_div, ← Matrix.trace_sum, ← Finset.sum_mul, twirl]
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, trace_onePauli_mul, trace_onePauli_mul]
  by_cases h1 : a = c <;> by_cases h2 : b = d
  · subst h1; subst h2; simp; norm_num
  · have h2' : ¬ d = b := fun h => h2 h.symm
    simp [h1, h2, h2']
  · simp [h1, h2]
  · simp [h1, h2]


lemma paulisOn_eq_piFinset {n : ℕ} (S : Finset (Fin n)) :
    paulisOn S = Fintype.piFinset (fun i => if i ∈ S then (Finset.univ : Finset (Fin 4)) else {0}) := by
  ext R
  rw [paulisOn, Finset.mem_filter, Fintype.mem_piFinset]
  simp only [Finset.mem_univ, true_and, support, Finset.subset_iff, Finset.mem_filter]
  constructor
  · intro h i
    by_cases hi : i ∈ S
    · simp [hi]
    · simp only [hi, if_false, Finset.mem_singleton]
      by_contra hR
      exact hi (h hR)
  · intro h i hi
    by_contra hiS
    have := h i
    simp [hiS] at this
    exact hi this

lemma pauliAvg_prod {n : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin 4 → ℂ) :
    pauliAvg S (fun R => ∏ i, f i (R i)) =
      ∏ i, (if i ∈ S then (∑ r, f i r) / 4 else f i 0) := by
  rw [pauliAvg, paulisOn_eq_piFinset, ← Finset.prod_univ_sum]
  have h4 : (4 : ℂ) ^ S.card = ∏ i, (if i ∈ S then (4 : ℂ) else 1) := by
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  rw [h4, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  by_cases hi : i ∈ S <;> simp [hi]

theorem lemma_2_8_aux {n : ℕ} (P1 P2 Q1 Q2 : Pauli n) (S : Finset (Fin n))
    (hS : pairSupport (P1, P2) ⊆ S) :
    pauliAvg S (fun R => ntr ((chi P1 P2 (pauliMatrix R))ᴴ * chi Q1 Q2 (pauliMatrix R))) =
      if restrict S Q1 = P1 ∧ restrict S Q2 = P2 ∧ restrict Sᶜ Q1 = restrict Sᶜ Q2 then 1 else 0 := by
  have hP : ∀ i, i ∉ S → P1 i = 0 ∧ P2 i = 0 := by
    intro i hi
    constructor
    · by_contra h
      exact hi (hS (by simp [pairSupport, support, h]))
    · by_contra h
      exact hi (hS (by simp [pairSupport, support, h]))
  have hexpr : ∀ R : Pauli n, ntr ((chi P1 P2 (pauliMatrix R))ᴴ * chi Q1 Q2 (pauliMatrix R)) =
      ∏ i, ((onePauli (P1 i) * onePauli (R i) * onePauli (P2 i))ᴴ *
        (onePauli (Q1 i) * onePauli (R i) * onePauli (Q2 i))).trace / 2 := by
    intro R
    simp only [chi, pauliMatrix_eq_tens, tens_mul, tens_conjTranspose, ntr_tens]
  simp_rw [hexpr]
  rw [pauliAvg_prod S (fun i r => ((onePauli (P1 i) * onePauli r * onePauli (P2 i))ᴴ *
        (onePauli (Q1 i) * onePauli r * onePauli (Q2 i))).trace / 2)]
  have hfac : ∀ i, (if i ∈ S then (∑ r, ((onePauli (P1 i) * onePauli r * onePauli (P2 i))ᴴ *
        (onePauli (Q1 i) * onePauli r * onePauli (Q2 i))).trace / 2) / 4 else
        ((onePauli (P1 i) * onePauli 0 * onePauli (P2 i))ᴴ *
        (onePauli (Q1 i) * onePauli 0 * onePauli (Q2 i))).trace / 2) =
      if (if i ∈ S then (P1 i = Q1 i ∧ P2 i = Q2 i) else Q1 i = Q2 i) then 1 else 0 := by
    intro i
    by_cases hi : i ∈ S
    · simp only [hi, if_true]
      exact single_avg _ _ _ _
    · simp only [hi, if_false]
      obtain ⟨h1, h2⟩ := hP i hi
      rw [h1, h2, onePauli_zero]
      simp only [Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one]
      rw [trace_onePauli_mul]
      by_cases h : Q1 i = Q2 i <;> simp [h]
  simp_rw [hfac]
  rw [Finset.prod_boole]
  congr 1
  apply propext
  simp only [Finset.mem_univ, true_implies]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · funext i
      by_cases hi : i ∈ S
      · have := h i; simp [hi] at this; simp [restrict, hi, this.1]
      · simp [restrict, hi, (hP i hi).1]
    · funext i
      by_cases hi : i ∈ S
      · have := h i; simp [hi] at this; simp [restrict, hi, this.2]
      · simp [restrict, hi, (hP i hi).2]
    · funext i
      by_cases hi : i ∈ S
      · simp [restrict, hi]
      · have := h i; simp [hi] at this; simp [restrict, hi, this]
  · rintro ⟨h1, h2, h3⟩ i
    by_cases hi : i ∈ S
    · have e1 := congrFun h1 i
      have e2 := congrFun h2 i
      simp [restrict, hi] at e1 e2
      simp [hi, e1, e2]
    · have e3 := congrFun h3 i
      simp [restrict, hi] at e3
      simp [hi, e3]

theorem lemma_2_7_aux {n : ℕ} (P1 P2 Q1 Q2 : Pauli n) :
    pauliAvg Finset.univ (fun R =>
      ntr ((chi P1 P2 (pauliMatrix R))ᴴ * chi Q1 Q2 (pauliMatrix R))) =
      if P1 = Q1 ∧ P2 = Q2 then 1 else 0 := by
  rw [lemma_2_8_aux P1 P2 Q1 Q2 Finset.univ (Finset.subset_univ _)]
  have hr : ∀ Q : Pauli n, restrict Finset.univ Q = Q := fun Q => by
    funext i; simp [restrict]
  have hr' : ∀ Q : Pauli n, restrict (Finset.univ : Finset (Fin n))ᶜ Q = 0 := fun Q => by
    funext i; simp [restrict]
  simp only [hr, hr', and_true]
  by_cases h1 : P1 = Q1 <;> by_cases h2 : P2 = Q2 <;> simp [h1, h2, eq_comm]

end LindbladStructLearn.FourierAux

open LindbladTolerant.Testing LindbladStructLearn LindbladStructLearn.FourierAux

theorem solution {n : ℕ} (P1 P2 Q1 Q2 : Pauli n) :
    pauliAvg Finset.univ (fun R =>
      ntr ((chi P1 P2 (pauliMatrix R))ᴴ * chi Q1 Q2 (pauliMatrix R))) =
      if P1 = Q1 ∧ P2 = Q2 then 1 else 0 :=
  lemma_2_7_aux P1 P2 Q1 Q2
