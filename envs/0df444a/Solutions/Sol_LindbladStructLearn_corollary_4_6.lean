-- Prove2me | solution 1 for LindbladStructLearn.corollary_4_6
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:10:32.830825+00:00
-- url     : https://prove2.me/submissions/90af435c-74db-4e6e-8c30-e6fcb7a2c1ef

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_LindbladStructLearn_lindbladAdj
import Definitions.Def_LindbladStructLearn_IsKLocal
import Definitions.Def_LindbladStructLearn_b1Norm
import Definitions.Def_LindbladStructLearn_Amat
import Definitions.Def_LindbladStructLearn_Vmat
import Definitions.Def_LindbladStructLearn_alg1Sample
import Definitions.Def_LindbladStructLearn_bornAmp
import Definitions.Def_LindbladStructLearn_alg3Law
import Definitions.Def_LindbladStructLearn_alg2Law
import Definitions.Def_LindbladStructLearn_Eell
import Definitions.Def_LindbladStructLearn_Etrunc
import Definitions.Def_LindbladStructLearn_ext
import Definitions.Def_LindbladStructLearn_FinDist_expect
import Definitions.Def_LindbladStructLearn_locFourier
import Definitions.Def_LindbladStructLearn_toIdx

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



namespace LindbladStructLearn.AAux
open LindbladTolerant.Testing LindbladStructLearn

variable {n : ℕ}

lemma mem_support_iff (p : Pauli n) (i : Fin n) : i ∈ support p ↔ p i ≠ 0 := by
  simp [support]

lemma not_mem_support_iff (p : Pauli n) (i : Fin n) : i ∉ support p ↔ p i = 0 := by
  simp [support]

lemma mem_pairSupport_iff (P : Pauli n × Pauli n) (i : Fin n) :
    i ∈ pairSupport P ↔ P.1 i ≠ 0 ∨ P.2 i ≠ 0 := by
  simp [pairSupport, support]

lemma not_mem_pairSupport_iff (P : Pauli n × Pauli n) (i : Fin n) :
    i ∉ pairSupport P ↔ P.1 i = 0 ∧ P.2 i = 0 := by
  simp [pairSupport, support]

lemma confuses_iff (Q P : Pauli n × Pauli n) : confuses Q P ↔
    (∀ i ∈ pairSupport P, Q.1 i = P.1 i ∧ Q.2 i = P.2 i) ∧
      (∀ i ∉ pairSupport P, Q.1 i = Q.2 i) := by
  unfold confuses restrict
  simp only [funext_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i hi => ⟨?_, ?_⟩, fun i hi => ?_⟩
    · have := h1 i; simpa [hi] using this
    · have := h2 i; simpa [hi] using this
    · have := h3 i; simpa [hi] using this
  · rintro ⟨h1, h3⟩
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
    · by_cases hi : i ∈ pairSupport P
      · simp [hi, (h1 i hi).1]
      · simp [hi, ((not_mem_pairSupport_iff P i).1 hi).1]
    · by_cases hi : i ∈ pairSupport P
      · simp [hi, (h1 i hi).2]
      · simp [hi, ((not_mem_pairSupport_iff P i).1 hi).2]
    · by_cases hi : i ∈ pairSupport P
      · simp [hi]
      · simp [hi, h3 i hi]

lemma confuses_refl (P : Pauli n × Pauli n) : confuses P P := by
  rw [confuses_iff]
  refine ⟨fun i _ => ⟨rfl, rfl⟩, fun i hi => ?_⟩
  rw [not_mem_pairSupport_iff] at hi
  rw [hi.1, hi.2]

lemma confuses_support {Q P : Pauli n × Pauli n} (h : confuses Q P) :
    pairSupport P ⊆ pairSupport Q := by
  intro i hi
  rw [confuses_iff] at h
  obtain ⟨e1, e2⟩ := h.1 i hi
  rw [mem_pairSupport_iff] at hi ⊢
  rw [e1, e2]; exact hi

lemma confuses_trans {R Q P : Pauli n × Pauli n} (h1 : confuses R Q) (h2 : confuses Q P) :
    confuses R P := by
  have hs := confuses_support h2
  rw [confuses_iff] at h1 h2 ⊢
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨a, b⟩ := h1.1 i (hs hi)
    obtain ⟨c, d⟩ := h2.1 i hi
    exact ⟨a.trans c, b.trans d⟩
  · by_cases hq : i ∈ pairSupport Q
    · obtain ⟨a, b⟩ := h1.1 i hq
      rw [a, b]; exact h2.2 i hi
    · exact h1.2 i hq

lemma confuses_eq_of_support {Q P : Pauli n × Pauli n} (h : confuses Q P)
    (hs : pairSupport Q ⊆ pairSupport P) : Q = P := by
  rw [confuses_iff] at h
  ext : 1
  · funext i
    by_cases hi : i ∈ pairSupport P
    · exact (h.1 i hi).1
    · have hq : i ∉ pairSupport Q := fun hq => hi (hs hq)
      rw [((not_mem_pairSupport_iff Q i).1 hq).1, ((not_mem_pairSupport_iff P i).1 hi).1]
  · funext i
    by_cases hi : i ∈ pairSupport P
    · exact (h.1 i hi).2
    · have hq : i ∉ pairSupport Q := fun hq => hi (hs hq)
      rw [((not_mem_pairSupport_iff Q i).1 hq).2, ((not_mem_pairSupport_iff P i).1 hi).2]

/-- the intermediate pair determined by a set `T` -/
def mid (A : Finset (Fin n)) (c : Pauli n × Pauli n) : Pauli n × Pauli n :=
  (fun i => if i ∈ A then c.1 i else 0, fun i => if i ∈ A then c.2 i else 0)

lemma mid_support {a c : Pauli n × Pauli n} (h : confuses c a) {T : Finset (Fin n)}
    (hT : T ⊆ pairSupport c \ pairSupport a) :
    pairSupport (mid (pairSupport a ∪ T) c) = pairSupport a ∪ T := by
  have hs := confuses_support h
  rw [confuses_iff] at h
  ext i
  rw [mem_pairSupport_iff]
  simp only [mid]
  by_cases hA : i ∈ pairSupport a ∪ T
  · simp only [hA, if_true, iff_true]
    rcases Finset.mem_union.1 hA with ha | ht
    · rw [(h.1 i ha).1, (h.1 i ha).2]; exact (mem_pairSupport_iff a i).1 ha
    · have := hT ht
      rw [Finset.mem_sdiff] at this
      exact (mem_pairSupport_iff c i).1 this.1
  · simp [hA]

lemma mid_between {a c : Pauli n × Pauli n} (h : confuses c a) {T : Finset (Fin n)}
    (hT : T ⊆ pairSupport c \ pairSupport a) :
    confuses (mid (pairSupport a ∪ T) c) a ∧ confuses c (mid (pairSupport a ∪ T) c) := by
  have hsupp := mid_support h hT
  have h' := h
  rw [confuses_iff] at h'
  constructor
  · rw [confuses_iff]
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · simp only [mid, Finset.mem_union, hi, true_or, if_true]
      exact h'.1 i hi
    · simp only [mid]
      by_cases ht : i ∈ pairSupport a ∪ T
      · simp only [ht, if_true]; exact h'.2 i hi
      · simp [ht]
  · rw [confuses_iff, hsupp]
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · simp only [mid, if_pos hi]; simp
    · rw [Finset.mem_union, not_or] at hi
      exact h'.2 i hi.1

lemma mid_eq {a b c : Pauli n × Pauli n} (h1 : confuses b a) (h2 : confuses c b) :
    mid (pairSupport a ∪ (pairSupport b \ pairSupport a)) c = b := by
  have hs := confuses_support h1
  rw [Finset.union_sdiff_of_subset hs]
  rw [confuses_iff] at h2
  ext : 1
  · funext i
    simp only [mid]
    by_cases hi : i ∈ pairSupport b
    · simp [hi, (h2.1 i hi).1]
    · simp [hi, ((not_mem_pairSupport_iff b i).1 hi).1]
  · funext i
    simp only [mid]
    by_cases hi : i ∈ pairSupport b
    · simp [hi, (h2.1 i hi).2]
    · simp [hi, ((not_mem_pairSupport_iff b i).1 hi).2]

open Classical in
/-- Möbius inversion for the confusion order (Helper Lemma 3.4). -/
lemma mobius (a c : Pauli n × Pauli n) :
    ∑ b : Pauli n × Pauli n, (if confuses b a ∧ confuses c b then
      ((-1 : ℂ)) ^ ((pairSupport b).card - (pairSupport a).card) else 0) =
      if c = a then 1 else 0 := by
  classical
  by_cases h : confuses c a
  · rw [← Finset.sum_filter]
    have key : ∑ b ∈ Finset.univ.filter (fun b => confuses b a ∧ confuses c b),
        ((-1 : ℂ)) ^ ((pairSupport b).card - (pairSupport a).card) =
        ∑ T ∈ (pairSupport c \ pairSupport a).powerset, ((-1 : ℂ)) ^ T.card := by
      refine Finset.sum_bij' (fun b _ => pairSupport b \ pairSupport a)
        (fun T _ => mid (pairSupport a ∪ T) c) ?_ ?_ ?_ ?_ ?_
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        simp only [Finset.mem_powerset]
        exact Finset.sdiff_subset_sdiff (confuses_support hb.2) le_rfl
      · intro T hT
        simp only [Finset.mem_powerset] at hT
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact mid_between h hT
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        exact mid_eq hb.1 hb.2
      · intro T hT
        simp only [Finset.mem_powerset] at hT
        rw [mid_support h hT]
        rw [Finset.union_sdiff_left]
        apply Finset.sdiff_eq_self_of_disjoint
        exact Finset.disjoint_of_subset_left hT Finset.sdiff_disjoint
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        rw [Finset.card_sdiff_of_subset (confuses_support hb.1)]
    rw [key]
    have := congrArg (fun z : ℤ => (z : ℂ))
      (Finset.sum_powerset_neg_one_pow_card (x := pairSupport c \ pairSupport a))
    simp only [Int.cast_sum, Int.cast_pow, Int.cast_neg, Int.cast_one] at this
    rw [this]
    by_cases hca : c = a
    · subst hca; simp
    · have hne : pairSupport c \ pairSupport a ≠ ∅ := by
        intro he
        apply hca
        apply confuses_eq_of_support h
        rw [Finset.sdiff_eq_empty_iff_subset] at he
        exact he
      simp [hne, hca]
  · have hca : c ≠ a := fun e => h (e ▸ confuses_refl c)
    rw [if_neg hca]
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact h (confuses_trans h2 h1)

end LindbladStructLearn.AAux


namespace LindbladStructLearn.AAux
open LindbladTolerant.Testing LindbladStructLearn LindbladStructLearn.FourierAux

variable {n : ℕ}

lemma onePauli_mul (a b : Fin 4) :
    onePauli a * onePauli b = letterPhase a b • onePauli (letterMul a b) := by
  ext x y
  fin_cases a <;> fin_cases b <;> cases x <;> cases y <;>
    simp [onePauli, letterPhase, letterMul, Matrix.mul_apply]

lemma tens_smul (c : Fin n → ℂ) (a : Fin n → Op Bool) :
    tens (fun i => c i • a i) = (∏ i, c i) • tens a := by
  ext x y
  simp [tens, Finset.prod_mul_distrib]

lemma pauliMatrix_mul (P Q : Pauli n) :
    pauliMatrix P * pauliMatrix Q = pauliPhase P Q • pauliMatrix (pauliProd P Q) := by
  rw [pauliMatrix_eq_tens, pauliMatrix_eq_tens, tens_mul]
  simp_rw [onePauli_mul]
  rw [tens_smul]
  rfl

lemma pauliMatrix_zero : pauliMatrix (0 : Pauli n) = 1 := by
  rw [pauliMatrix_eq_tens]
  simp only [Pi.zero_apply, onePauli_zero]
  ext x y
  simp only [tens, Matrix.one_apply]
  rw [Finset.prod_boole]
  simp [funext_iff]

lemma applySuper_leftRight {I : Type*} [Fintype I] [DecidableEq I] (a b X : Op I) :
    applySuper (leftRight a b) X = a * X * b := by
  ext i j
  simp only [applySuper, leftRight, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun r _ => ?_))
  ring

lemma applySuper_add {I : Type*} [Fintype I] [DecidableEq I] (g h : Super I I) (X : Op I) :
    applySuper (g + h) X = applySuper g X + applySuper h X := by
  ext i j
  simp [applySuper, add_mul, Finset.sum_add_distrib]

lemma applySuper_sub {I : Type*} [Fintype I] [DecidableEq I] (g h : Super I I) (X : Op I) :
    applySuper (g - h) X = applySuper g X - applySuper h X := by
  ext i j
  simp [applySuper, sub_mul, Finset.sum_sub_distrib]

lemma applySuper_smul {I : Type*} [Fintype I] [DecidableEq I] (c : ℂ) (g : Super I I) (X : Op I) :
    applySuper (c • g) X = c • applySuper g X := by
  ext i j
  simp [applySuper, mul_assoc, Finset.mul_sum]

lemma applySuper_sum {I : Type*} [Fintype I] [DecidableEq I] {ι : Type*} (s : Finset ι)
    (g : ι → Super I I) (X : Op I) :
    applySuper (∑ a ∈ s, g a) X = ∑ a ∈ s, applySuper (g a) X := by
  classical
  induction s using Finset.induction_on with
  | empty => ext i j; simp [applySuper]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, applySuper_add, ih]

/-- the single Lindblad term superoperator -/
def termSuper (Q : Pauli n × Pauli n) : Super (Qubits n) (Qubits n) :=
  leftRight (pauliMatrix Q.1) (pauliMatrix Q.2) -
      (1 / 2 : ℂ) • (leftRight (pauliMatrix Q.2 * pauliMatrix Q.1) 1 +
        leftRight 1 (pauliMatrix Q.2 * pauliMatrix Q.1))

lemma lindbladSuper_eq (x : Pauli n × Pauli n → ℂ) :
    lindbladSuper x = ∑ P ∈ Finset.univ.filter (fun P : Pauli n × Pauli n => P.1 ≠ 0),
      x P • termSuper P := rfl

lemma ext_single {k : ℕ} (b : Idx n k) (P : Pauli n × Pauli n) :
    ext (Pi.single b (1 : ℂ)) P = if P = b.1 then 1 else 0 := by
  unfold ext
  split_ifs with h1 h2 h2
  · subst h2; simp
  · rw [Pi.single_apply, if_neg]
    intro e; apply h2; rw [← e]
  · exact absurd (h2 ▸ b.2) h1
  · rfl

lemma lindbladSuper_single {k : ℕ} (b : Idx n k) :
    lindbladSuper (ext (Pi.single b (1 : ℂ))) = termSuper b.1 := by
  rw [lindbladSuper_eq]
  rw [Finset.sum_eq_single b.1]
  · rw [ext_single, if_pos rfl, one_smul]
  · intro P _ hP
    rw [ext_single, if_neg hP, zero_smul]
  · intro h
    exfalso; apply h
    simp [b.2.1]

lemma applySuper_termSuper (Q : Pauli n × Pauli n) (X : Op (Qubits n)) :
    applySuper (termSuper Q) X =
      chi Q.1 Q.2 X - ((1 / 2 : ℂ) * pauliPhase Q.2 Q.1) •
        (chi (pauliProd Q.2 Q.1) 0 X + chi 0 (pauliProd Q.2 Q.1) X) := by
  rw [termSuper, applySuper_sub, applySuper_smul, applySuper_add, applySuper_leftRight,
    applySuper_leftRight, applySuper_leftRight, pauliMatrix_mul]
  simp only [chi, pauliMatrix_zero, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_add, smul_smul]

lemma pauliAvg_add (S : Finset (Fin n)) (f g : Pauli n → ℂ) :
    pauliAvg S (fun R => f R + g R) = pauliAvg S f + pauliAvg S g := by
  simp [pauliAvg, Finset.sum_add_distrib, add_div]

lemma pauliAvg_sub (S : Finset (Fin n)) (f g : Pauli n → ℂ) :
    pauliAvg S (fun R => f R - g R) = pauliAvg S f - pauliAvg S g := by
  simp [pauliAvg, Finset.sum_sub_distrib, sub_div]

lemma pauliAvg_mul (S : Finset (Fin n)) (c : ℂ) (f : Pauli n → ℂ) :
    pauliAvg S (fun R => c * f R) = c * pauliAvg S f := by
  rw [pauliAvg, pauliAvg, ← Finset.mul_sum, mul_div_assoc]

lemma ntr_add (A B : Op (Qubits n)) : ntr (A + B) = ntr A + ntr B := by
  simp [ntr, Matrix.trace_add, add_div]

lemma ntr_sub (A B : Op (Qubits n)) : ntr (A - B) = ntr A - ntr B := by
  simp [ntr, Matrix.trace_sub, sub_div]

lemma ntr_smul (c : ℂ) (A : Op (Qubits n)) : ntr (c • A) = c * ntr A := by
  simp [ntr, Matrix.trace_smul, mul_div_assoc]

open Classical in
lemma locChi (P Q : Pauli n × Pauli n) :
    pauliAvg (pairSupport P) (fun R =>
      ntr ((chi P.1 P.2 (pauliMatrix R))ᴴ * chi Q.1 Q.2 (pauliMatrix R))) =
      if confuses Q P then 1 else 0 := by
  rw [lemma_2_8_aux P.1 P.2 Q.1 Q.2 (pairSupport P) (by simp)]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl

lemma confuses_W0 (W : Pauli n) (a : Pauli n × Pauli n) :
    confuses (W, 0) a ↔ a.2 = 0 ∧ W = a.1 := by
  rw [confuses_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have ha2 : a.2 = 0 := by
      funext i
      by_cases hi : i ∈ pairSupport a
      · exact ((h1 i hi).2).symm
      · exact ((not_mem_pairSupport_iff a i).1 hi).2
    refine ⟨ha2, ?_⟩
    funext i
    by_cases hi : i ∈ pairSupport a
    · exact (h1 i hi).1
    · have e := h2 i hi
      simp only at e
      rw [e, ((not_mem_pairSupport_iff a i).1 hi).1]; rfl
  · rintro ⟨h1, h2⟩
    subst h2
    refine ⟨fun i _ => ⟨rfl, by simp [h1]⟩, fun i hi => ?_⟩
    exact ((not_mem_pairSupport_iff a i).1 hi).1

lemma not_confuses_0W (W : Pauli n) (a : Pauli n × Pauli n) (ha : a.1 ≠ 0) :
    ¬ confuses (0, W) a := by
  rw [confuses_iff]
  rintro ⟨h1, _⟩
  apply ha
  funext i
  by_cases hi : i ∈ pairSupport a
  · exact ((h1 i hi).1).symm
  · exact ((not_mem_pairSupport_iff a i).1 hi).1

open Classical in
lemma Amat_apply {k : ℕ} (a b : Idx n k) :
    Amat n k a b = (if confuses b.1 a.1 then 1 else 0) -
      (1 / 2 : ℂ) * (if a.1.2 = 0 ∧ pauliProd b.1.2 b.1.1 = a.1.1 then
        pauliPhase b.1.2 b.1.1 else 0) := by
  unfold Amat locFourier
  rw [lindbladSuper_single]
  simp_rw [applySuper_termSuper, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_add, ntr_sub,
    ntr_smul, ntr_add, mul_add]
  rw [pauliAvg_sub, pauliAvg_add, pauliAvg_mul, pauliAvg_mul, locChi a.1 b.1,
    locChi a.1 (pauliProd b.1.2 b.1.1, 0), locChi a.1 (0, pauliProd b.1.2 b.1.1)]
  rw [if_neg (not_confuses_0W _ _ a.2.1)]
  by_cases h : a.1.2 = 0 ∧ pauliProd b.1.2 b.1.1 = a.1.1
  · have hc : confuses (pauliProd b.1.2 b.1.1, 0) a.1 := (confuses_W0 _ _).2 ⟨h.1, h.2⟩
    simp only [if_pos hc, if_pos h]
    ring
  · have hc : ¬ confuses (pauliProd b.1.2 b.1.1, 0) a.1 := fun h' => h ((confuses_W0 _ _).1 h')
    simp only [if_neg hc, if_neg h]
    ring

end LindbladStructLearn.AAux


namespace LindbladStructLearn.AAux
open LindbladTolerant.Testing LindbladStructLearn LindbladStructLearn.FourierAux

variable {n : ℕ}

lemma letterMul_eq_zero_iff (x y : Fin 4) : letterMul x y = 0 ↔ x = y := by
  fin_cases x <;> fin_cases y <;> simp [letterMul]

lemma letterMul_eq_iff (y x p : Fin 4) : letterMul y x = p ↔ y = letterMul p x := by
  fin_cases x <;> fin_cases y <;> fin_cases p <;> simp [letterMul]

lemma letterMul_zero_left (x : Fin 4) : letterMul 0 x = x := by
  fin_cases x <;> simp [letterMul]

lemma letterMul_self (x : Fin 4) : letterMul x x = 0 := by
  fin_cases x <;> simp [letterMul]

lemma letterMul_zero_right (x : Fin 4) : letterMul x 0 = x := by
  fin_cases x <;> simp [letterMul]

lemma letterPhase_self (x : Fin 4) : letterPhase x x = 1 := by
  fin_cases x <;> simp [letterPhase]

lemma letterPhase_zero_left (x : Fin 4) : letterPhase 0 x = 1 := by
  fin_cases x <;> simp [letterPhase]

lemma letterPhase_zero_right (x : Fin 4) : letterPhase x 0 = 1 := by
  fin_cases x <;> simp [letterPhase]

lemma letterPhase_mul (p q : Fin 4) : letterPhase (letterMul p q) q = star (letterPhase p q) := by
  fin_cases p <;> fin_cases q <;> simp [letterPhase, letterMul]

lemma pauliProd_eq_zero_iff (P Q : Pauli n) : pauliProd P Q = 0 ↔ P = Q := by
  simp only [funext_iff, pauliProd, Pi.zero_apply, letterMul_eq_zero_iff]

lemma pauliProd_eq_iff (Y X P : Pauli n) : pauliProd Y X = P ↔ Y = pauliProd P X := by
  simp only [funext_iff, pauliProd, letterMul_eq_iff]

/-- sum over the index set of a function of the underlying pair that vanishes off it -/
lemma sum_Idx {k : ℕ} (f : Pauli n × Pauli n → ℂ)
    (hf : ∀ P : Pauli n × Pauli n, ¬ (P.1 ≠ 0 ∧ (pairSupport P).card ≤ k) → f P = 0) :
    ∑ b : Idx n k, f b.1 = ∑ P, f P := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun P : Pauli n × Pauli n =>
    P.1 ≠ 0 ∧ (pairSupport P).card ≤ k)) (by simp) f]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro P _ hP
  apply hf
  simpa using hP

lemma sum_Idx_ite_eq {k : ℕ} (p : Pauli n × Pauli n) (v : ℂ) [∀ b : Idx n k, Decidable (b.1 = p)] :
    ∑ b : Idx n k, (if b.1 = p then v else 0) =
      if p.1 ≠ 0 ∧ (pairSupport p).card ≤ k then v else 0 := by
  classical
  split_ifs with hp
  · rw [Finset.sum_eq_single (⟨p, hp⟩ : Idx n k)]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro e; apply hb; exact Subtype.ext e
    · simp
  · apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro e; apply hp; rw [← e]; exact b.2

lemma pairSupport_P0 (P : Pauli n) : pairSupport (P, 0) = support P := by
  ext i; simp [pairSupport, support]

lemma pairSupport_0P (P : Pauli n) : pairSupport (0, P) = support P := by
  ext i; simp [pairSupport, support]

lemma confuses_P0_iff (P : Pauli n) (c : Pauli n × Pauli n) :
    confuses c (P, 0) ↔ c.2 = pauliProd P c.1 ∧ restrict (support P) c.1 = P := by
  rw [confuses_iff, pairSupport_P0]
  simp only [funext_iff, pauliProd, restrict]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    · by_cases hi : i ∈ support P
      · rw [(h1 i hi).1, (h1 i hi).2, letterMul_self]; rfl
      · rw [(not_mem_support_iff P i).1 hi, letterMul_zero_left]; exact (h2 i hi).symm
    · by_cases hi : i ∈ support P
      · simp [hi, (h1 i hi).1]
      · simp [hi, (not_mem_support_iff P i).1 hi]
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have e2 := h2 i
      simp only [hi, if_true] at e2
      refine ⟨e2, ?_⟩
      rw [h1 i, e2, letterMul_self]; rfl
    · rw [h1 i, (not_mem_support_iff P i).1 hi, letterMul_zero_left]

lemma confuses_0P_iff (P : Pauli n) (c : Pauli n × Pauli n) :
    confuses c (0, P) ↔ c.2 = pauliProd P c.1 ∧ restrict (support P) c.1 = 0 := by
  rw [confuses_iff, pairSupport_0P]
  simp only [funext_iff, pauliProd, restrict]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    · by_cases hi : i ∈ support P
      · rw [(h1 i hi).1, (h1 i hi).2]; simp [letterMul_zero_right]
      · rw [(not_mem_support_iff P i).1 hi, letterMul_zero_left]; exact (h2 i hi).symm
    · by_cases hi : i ∈ support P
      · simp [hi, (h1 i hi).1]
      · simp [hi]
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have e2 := h2 i
      simp only [hi, if_true] at e2
      refine ⟨e2, ?_⟩
      rw [h1 i, e2]; simp [letterMul_zero_right]
    · rw [h1 i, (not_mem_support_iff P i).1 hi, letterMul_zero_left]

lemma pairSupport_QPQ (P Q : Pauli n) (hQ : support Q ⊆ support P) :
    pairSupport (Q, pauliProd P Q) = support P := by
  ext i
  rw [mem_pairSupport_iff, mem_support_iff]
  simp only [pauliProd]
  constructor
  · rintro (h | h)
    · exact (mem_support_iff P i).1 (hQ ((mem_support_iff Q i).2 h))
    · intro hp; apply h; rw [hp, letterMul_zero_left]
      exact (not_mem_support_iff Q i).1 (fun hq => (mem_support_iff P i).1 (hQ hq) hp)
  · intro hp
    by_cases hq : Q i = 0
    · right; rw [hq, letterMul_zero_right]; exact hp
    · left; exact hq

lemma confuses_QPQ_iff (P Q : Pauli n) (hQ : support Q ⊆ support P) (c : Pauli n × Pauli n) :
    confuses c (Q, pauliProd P Q) ↔ c.2 = pauliProd P c.1 ∧ restrict (support P) c.1 = Q := by
  rw [confuses_iff, pairSupport_QPQ P Q hQ]
  simp only [funext_iff, pauliProd, restrict]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    · by_cases hi : i ∈ support P
      · rw [(h1 i hi).1, (h1 i hi).2]
      · rw [(not_mem_support_iff P i).1 hi, letterMul_zero_left]; exact (h2 i hi).symm
    · by_cases hi : i ∈ support P
      · simp [hi, (h1 i hi).1]
      · simp only [hi, if_false]
        exact ((not_mem_support_iff Q i).1 (fun hq => hi (hQ hq))).symm
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have e2 := h2 i
      simp only [hi, if_true] at e2
      exact ⟨e2, by rw [h1 i, e2]⟩
    · rw [h1 i, (not_mem_support_iff P i).1 hi, letterMul_zero_left]

lemma restrict_support_sub (S : Finset (Fin n)) (Q : Pauli n) : support (restrict S Q) ⊆ S := by
  intro i hi
  rw [mem_support_iff] at hi
  by_contra h
  exact hi (by simp [restrict, h])

lemma phase_eq (P : Pauli n) (c : Pauli n × Pauli n) (H : c.2 = pauliProd P c.1) :
    pauliPhase c.2 c.1 = star (pauliPhase P (restrict (support P) c.1)) := by
  unfold pauliPhase
  rw [star_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [H]
  simp only [pauliProd, restrict]
  by_cases hi : i ∈ support P
  · simp only [hi, if_true]; exact letterPhase_mul _ _
  · rw [(not_mem_support_iff P i).1 hi, letterMul_zero_left, letterPhase_self]
    simp [letterPhase_zero_left]

lemma star_phase_P (P : Pauli n) : star (pauliPhase P P) = 1 := by
  simp [pauliPhase, letterPhase_self]

lemma star_phase_0 (P : Pauli n) : star (pauliPhase P 0) = 1 := by
  simp [pauliPhase, letterPhase_zero_right]

end LindbladStructLearn.AAux


namespace LindbladStructLearn.AAux
open LindbladTolerant.Testing LindbladStructLearn LindbladStructLearn.FourierAux

variable {n : ℕ}

open Classical in
lemma Vmat_apply_ne {k : ℕ} (a b : Idx n k) (ha : a.1.2 ≠ 0) :
    Vmat n k a b = if confuses b.1 a.1 then
      (-1 : ℂ) ^ ((pairSupport b.1).card - (pairSupport a.1).card) else 0 := by
  unfold Vmat
  simp only [ha, ne_eq, not_false_eq_true, if_true]

open Classical in
lemma Vmat_apply_eq {k : ℕ} (a b : Idx n k) (ha : a.1.2 = 0) :
    Vmat n k a b =
      (if b.1 = a.1 then 2 else 0) +
      (if support b.1.1 ⊆ support a.1.1 ∧ b.1.1 ≠ 0 ∧ b.1.1 ≠ a.1.1 ∧
          b.1.2 = pauliProd a.1.1 b.1.1 then star (pauliPhase a.1.1 b.1.1) else 0) +
      (if confuses b.1 a.1 ∧ b.1 ≠ a.1 then
        (-1 : ℂ) ^ ((pairSupport b.1).card - (pairSupport a.1).card) else 0) -
      (if confuses b.1 (0, a.1.1) ∧ b.1 ≠ (0, a.1.1) then
        (-1 : ℂ) ^ ((pairSupport b.1).card - (pairSupport a.1).card) else 0) := by
  unfold Vmat
  simp only [ha, ne_eq, not_true_eq_false, if_false]


lemma confuses_ne_zero_1 {Q P : Pauli n × Pauli n} (h : confuses Q P) (hP : P.1 ≠ 0) : Q.1 ≠ 0 := by
  intro hQ
  apply hP
  rw [confuses_iff] at h
  funext i
  by_cases hi : i ∈ pairSupport P
  · rw [← (h.1 i hi).1, hQ]
  · exact ((not_mem_pairSupport_iff P i).1 hi).1

lemma confuses_ne_zero_2 {Q P : Pauli n × Pauli n} (h : confuses Q P) (hP : P.2 ≠ 0) : Q.2 ≠ 0 := by
  intro hQ
  apply hP
  rw [confuses_iff] at h
  funext i
  by_cases hi : i ∈ pairSupport P
  · rw [← (h.1 i hi).2, hQ]
  · exact ((not_mem_pairSupport_iff P i).1 hi).2

open Classical in
lemma mobius_Idx {k : ℕ} (a c : Idx n k) :
    ∑ b : Idx n k, (if confuses b.1 a.1 ∧ confuses c.1 b.1 then
      ((-1 : ℂ)) ^ ((pairSupport b.1).card - (pairSupport a.1).card) else 0) =
      if c.1 = a.1 then 1 else 0 := by
  rw [sum_Idx (fun b => if confuses b a.1 ∧ confuses c.1 b then
      ((-1 : ℂ)) ^ ((pairSupport b).card - (pairSupport a.1).card) else 0), mobius]
  intro P hP
  rw [if_neg]
  rintro ⟨h1, h2⟩
  apply hP
  exact ⟨confuses_ne_zero_1 h1 a.2.1, (Finset.card_le_card (confuses_support h2)).trans c.2.2⟩

open Classical in
theorem VA_one (k : ℕ) : Vmat n k * Amat n k = 1 := by
  ext a c
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hac : (a = c) ↔ (c.1 = a.1) := ⟨fun h => by rw [h], fun h => (Subtype.ext h).symm⟩
  simp_rw [Amat_apply]
  by_cases ha : a.1.2 ≠ 0
  · simp_rw [Vmat_apply_ne a _ ha]
    have hterm : ∀ b : Idx n k, (if confuses b.1 a.1 then
        (-1 : ℂ) ^ ((pairSupport b.1).card - (pairSupport a.1).card) else 0) *
        ((if confuses c.1 b.1 then 1 else 0) - (1 / 2 : ℂ) * (if b.1.2 = 0 ∧
          pauliProd c.1.2 c.1.1 = b.1.1 then pauliPhase c.1.2 c.1.1 else 0)) =
        if confuses b.1 a.1 ∧ confuses c.1 b.1 then
          (-1 : ℂ) ^ ((pairSupport b.1).card - (pairSupport a.1).card) else 0 := by
      intro b
      by_cases h1 : confuses b.1 a.1
      · have hb2 : b.1.2 ≠ 0 := confuses_ne_zero_2 h1 ha
        by_cases h2 : confuses c.1 b.1
        · simp [h1, h2, hb2]
        · simp [h1, h2, hb2]
      · simp [h1]
    simp_rw [hterm]
    rw [mobius_Idx]
    simp only [hac]
  · push Not at ha
    simp_rw [Vmat_apply_eq a _ ha]
    set P : Pauli n := a.1.1 with hPdef
    have hP : P ≠ 0 := a.2.1
    have haP : a.1 = (P, 0) := Prod.ext rfl ha
    have hSa : pairSupport a.1 = support P := by rw [haP, pairSupport_P0]
    set w : ℂ := pauliPhase c.1.2 c.1.1 with hw
    set Q0 : Pauli n := restrict (support P) c.1.1 with hQ0
    set H : Prop := c.1.2 = pauliProd P c.1.1 with hH
    -- the A entry
    set A : Idx n k → ℂ := fun b => (if confuses c.1 b.1 then 1 else 0) - (1 / 2 : ℂ) *
      (if b.1.2 = 0 ∧ pauliProd c.1.2 c.1.1 = b.1.1 then w else 0) with hA
    change ∑ b : Idx n k, (_ + _ + _ - _) * A b = _
    simp_rw [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    -- S1
    have S1 : ∑ b : Idx n k, (if b.1 = a.1 then (2 : ℂ) else 0) * A b = 2 * A a := by
      have : ∀ b : Idx n k, (if b.1 = a.1 then (2 : ℂ) else 0) * A b =
          if a = b then 2 * A a else 0 := by
        intro b
        by_cases hb : a = b
        · subst hb; simp
        · rw [if_neg hb, if_neg (fun e => hb (Subtype.ext e).symm), zero_mul]
      simp_rw [this]
      rw [Finset.sum_ite_eq]; simp
    -- S2
    have S2 : ∑ b : Idx n k, (if support b.1.1 ⊆ support a.1.1 ∧ b.1.1 ≠ 0 ∧ b.1.1 ≠ a.1.1 ∧
          b.1.2 = pauliProd a.1.1 b.1.1 then star (pauliPhase a.1.1 b.1.1) else 0) * A b =
        if H ∧ Q0 ≠ 0 ∧ Q0 ≠ P then star (pauliPhase P Q0) else 0 := by
      have : ∀ b : Idx n k, (if support b.1.1 ⊆ support a.1.1 ∧ b.1.1 ≠ 0 ∧ b.1.1 ≠ a.1.1 ∧
          b.1.2 = pauliProd a.1.1 b.1.1 then star (pauliPhase a.1.1 b.1.1) else 0) * A b =
          if b.1 = (Q0, pauliProd P Q0) then
            (if H ∧ Q0 ≠ 0 ∧ Q0 ≠ P then star (pauliPhase P Q0) else 0) else 0 := by
        intro b
        by_cases hb : support b.1.1 ⊆ support a.1.1 ∧ b.1.1 ≠ 0 ∧ b.1.1 ≠ a.1.1 ∧
            b.1.2 = pauliProd a.1.1 b.1.1
        · rw [if_pos hb]
          obtain ⟨hs, hne0, hneP, h2⟩ := hb
          have hbeq : b.1 = (b.1.1, pauliProd P b.1.1) := Prod.ext rfl h2
          have hb2 : b.1.2 ≠ 0 := by
            rw [h2]; intro e; rw [pauliProd_eq_zero_iff] at e; exact hneP e.symm
          have hAb : A b = if H ∧ Q0 = b.1.1 then 1 else 0 := by
            simp only [hA, if_neg (fun h : b.1.2 = 0 ∧ _ => hb2 h.1), mul_zero, sub_zero]
            rw [hbeq]
            simp only [confuses_QPQ_iff P b.1.1 hs]
            rfl
          rw [hAb]
          by_cases hq : Q0 = b.1.1
          · have e : b.1 = (Q0, pauliProd P Q0) := by rw [hq]; exact hbeq
            rw [if_pos e]
            by_cases hHH : H
            · rw [if_pos ⟨hHH, hq⟩, if_pos ⟨hHH, hq ▸ hne0, hq ▸ hneP⟩, mul_one, hq]
            · rw [if_neg (fun h => hHH h.1), if_neg (fun h => hHH h.1), mul_zero]
          · rw [if_neg (fun h => hq h.2), mul_zero, if_neg]
            intro e; apply hq; rw [e]
        · rw [if_neg hb, zero_mul]
          by_cases e : b.1 = (Q0, pauliProd P Q0)
          · rw [if_pos e, if_neg]
            rintro ⟨_, h0, hPP⟩
            apply hb
            rw [e]
            exact ⟨restrict_support_sub _ _, h0, hPP, rfl⟩
          · rw [if_neg e]
      simp_rw [this]
      rw [sum_Idx_ite_eq]
      by_cases hc : H ∧ Q0 ≠ 0 ∧ Q0 ≠ P
      · rw [if_pos hc, if_pos]
        refine ⟨hc.2.1, ?_⟩
        rw [pairSupport_QPQ P Q0 (restrict_support_sub _ _), ← hSa]
        exact a.2.2
      · rw [if_neg hc]; simp
    -- S3
    have S3 : ∑ b : Idx n k, (if confuses b.1 a.1 ∧ b.1 ≠ a.1 then
          (-1 : ℂ) ^ ((pairSupport b.1).card - (pairSupport a.1).card) else 0) * A b =
        (if c.1 = a.1 then 1 else 0) - (if confuses c.1 a.1 then 1 else 0) := by
      have : ∀ b : Idx n k, (if confuses b.1 a.1 ∧ b.1 ≠ a.1 then
          (-1 : ℂ) ^ ((pairSupport b.1).card - (pairSupport a.1).card) else 0) * A b =
          (if confuses b.1 a.1 ∧ confuses c.1 b.1 then
            (-1 : ℂ) ^ ((pairSupport b.1).card - (pairSupport a.1).card) else 0) -
          (if a = b then (if confuses c.1 a.1 then 1 else 0) else 0) := by
        intro b
        by_cases hba : a = b
        · subst hba
          simp [confuses_refl]
        · have hne : b.1 ≠ a.1 := fun e => hba (Subtype.ext e).symm
          rw [if_neg hba, sub_zero]
          by_cases h1 : confuses b.1 a.1
          · have hb2 : b.1.2 ≠ 0 := by
              intro hb0
              apply hne
              rw [haP] at h1 ⊢
              rw [confuses_P0_iff] at h1
              have := h1.1
              rw [hb0, eq_comm, pauliProd_eq_zero_iff] at this
              exact Prod.ext this.symm hb0
            simp only [hA, if_pos (And.intro h1 hne), if_neg (fun h : b.1.2 = 0 ∧ _ => hb2 h.1)]
            by_cases h2 : confuses c.1 b.1 <;> simp [h1, h2]
          · simp [h1]
      simp_rw [this]
      rw [Finset.sum_sub_distrib, mobius_Idx, Finset.sum_ite_eq]
      simp
    -- S4
    have S4 : ∑ b : Idx n k, (if confuses b.1 (0, a.1.1) ∧ b.1 ≠ (0, a.1.1) then
          (-1 : ℂ) ^ ((pairSupport b.1).card - (pairSupport a.1).card) else 0) * A b =
        - (if confuses c.1 (0, P) then 1 else 0) := by
      set F : Pauli n × Pauli n → ℂ := fun Q => if Q.1 ≠ 0 then (if confuses Q (0, P) ∧
          confuses c.1 Q then (-1 : ℂ) ^ ((pairSupport Q).card - (pairSupport a.1).card) else 0)
          else 0 with hF
      have : ∀ b : Idx n k, (if confuses b.1 (0, a.1.1) ∧ b.1 ≠ (0, a.1.1) then
          (-1 : ℂ) ^ ((pairSupport b.1).card - (pairSupport a.1).card) else 0) * A b = F b.1 := by
        intro b
        change (if confuses b.1 (0, P) ∧ b.1 ≠ (0, P) then
          (-1 : ℂ) ^ ((pairSupport b.1).card - (pairSupport a.1).card) else 0) * A b = F b.1
        simp only [hF, b.2.1, ne_eq, not_false_eq_true, if_true]
        have hne : b.1 ≠ (0, P) := fun e => b.2.1 (by rw [e])
        by_cases h1 : confuses b.1 (0, P)
        · have hb2 : b.1.2 ≠ 0 := confuses_ne_zero_2 h1 (by simpa using hP)
          rw [if_pos (And.intro h1 hne)]
          simp only [hA, if_neg (fun h : b.1.2 = 0 ∧ _ => hb2 h.1)]
          by_cases h2 : confuses c.1 b.1 <;> simp [h1, h2]
        · rw [if_neg (fun h => h1 h.1), if_neg (fun h => h1 h.1), zero_mul]
      rw [Finset.sum_congr rfl (fun b _ => this b), sum_Idx F]
      · simp only [hF]
        rw [show (∑ Q : Pauli n × Pauli n, if Q.1 ≠ 0 then (if confuses Q (0, P) ∧ confuses c.1 Q then
            (-1 : ℂ) ^ ((pairSupport Q).card - (pairSupport a.1).card) else 0) else 0) =
            (∑ Q : Pauli n × Pauli n, (if confuses Q (0, P) ∧ confuses c.1 Q then
            (-1 : ℂ) ^ ((pairSupport Q).card - (pairSupport (0, P)).card) else 0)) -
            ∑ Q : Pauli n × Pauli n, (if Q = (0, P) then
              (if confuses c.1 (0, P) then 1 else 0) else 0) by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun Q _ => ?_)
          have hcard : (pairSupport (0, P)).card = (pairSupport a.1).card := by
            rw [hSa, pairSupport_0P]
          rw [hcard]
          by_cases hQ : Q = (0, P)
          · subst hQ; rw [hcard, Nat.sub_self, pow_zero]; simp [confuses_refl]
          · rw [if_neg hQ, sub_zero]
            by_cases hQ1 : Q.1 = 0
            · rw [if_neg (not_not.2 hQ1), if_neg]
              rintro ⟨h1, _⟩
              apply hQ
              rw [confuses_iff, pairSupport_0P] at h1
              refine Prod.ext hQ1 ?_
              funext i
              by_cases hi : i ∈ support P
              · exact (h1.1 i hi).2
              · rw [← h1.2 i hi, hQ1]; exact ((not_mem_support_iff P i).1 hi).symm
            · rw [if_pos hQ1]]
        rw [mobius, Finset.sum_ite_eq']
        simp only [Finset.mem_univ, if_true]
        rw [if_neg (fun e => c.2.1 (by rw [e]))]
        ring
      · intro Q hQ
        simp only [hF]
        by_cases hQ1 : Q.1 ≠ 0
        · rw [if_pos hQ1, if_neg]
          rintro ⟨_, h2⟩
          exact hQ ⟨hQ1, (Finset.card_le_card (confuses_support h2)).trans c.2.2⟩
        · rw [if_neg hQ1]
    rw [S1, S2, S3, S4]
    -- final bookkeeping
    have hca : confuses c.1 a.1 ↔ H ∧ Q0 = P := by rw [haP, confuses_P0_iff]
    have hc0 : confuses c.1 (0, P) ↔ H ∧ Q0 = 0 := by rw [confuses_0P_iff]
    have hG : (a.1.2 = 0 ∧ pauliProd c.1.2 c.1.1 = a.1.1) ↔ H := by
      rw [pauliProd_eq_iff]; exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩
    simp only [hA]
    rw [if_congr hca rfl rfl, if_congr hc0 rfl rfl, if_congr hG rfl rfl]
    simp only [hac]
    by_cases hHH : H
    · have hwq : w = star (pauliPhase P Q0) := phase_eq P c.1 hHH
      by_cases hq : Q0 = P
      · have hq0 : Q0 ≠ 0 := by rw [hq]; exact hP
        simp only [hHH, hq, true_and, if_true, ne_eq, not_true_eq_false, and_false, if_false]
        rw [hwq, hq, star_phase_P]
        split_ifs <;> ring
      · by_cases hq0 : Q0 = 0
        · simp only [hHH, hq0, true_and, if_true, ne_eq, not_true_eq_false, and_false, if_false,
            false_and]
          have h0P : ¬ (0 : Pauli n) = P := fun e => hP e.symm
          simp only [h0P, if_false]
          rw [hwq, hq0, star_phase_0]
          split_ifs <;> ring
        · simp only [hHH, hq, hq0, true_and, if_true, ne_eq, not_false_eq_true, and_self,
            if_false]
          rw [hwq]
          split_ifs <;> ring
    · simp only [hHH, false_and, if_false]
      split_ifs <;> ring

end LindbladStructLearn.AAux


namespace LindbladStructLearn.AAux
open LindbladTolerant.Testing LindbladStructLearn LindbladStructLearn.FourierAux

variable {n : ℕ}

open Classical in
/-- site sum of an index-set vector -/
def ss {k : ℕ} (y : Idx n k → ℂ) (i : Fin n) : ℝ :=
  ∑ b : Idx n k, if i ∈ pairSupport b.1 then ‖y b‖ else 0

lemma ss_nonneg {k : ℕ} (y : Idx n k → ℂ) (i : Fin n) : 0 ≤ ss y i := by
  unfold ss
  apply Finset.sum_nonneg
  intro b _
  split_ifs <;> simp

open Classical in
lemma site_eq {k : ℕ} (y : Idx n k → ℂ) (i : Fin n) :
    ((∑ P ∈ Finset.univ.filter (fun P : Pauli n × Pauli n => P.1 ≠ 0 ∧ i ∈ pairSupport P),
      ‖ext y P‖₊ : ℝ≥0) : ℝ) = ss y i := by
  rw [NNReal.coe_sum]
  simp only [coe_nnnorm]
  unfold ss
  let g : Pauli n × Pauli n → ℝ := fun P =>
    if h : P.1 ≠ 0 ∧ (pairSupport P).card ≤ k then
      (if i ∈ pairSupport P then ‖y ⟨P, h⟩‖ else 0) else 0
  have hg : ∀ b : Idx n k, (if i ∈ pairSupport b.1 then ‖y b‖ else 0) = g b.1 := by
    intro b; simp only [g, dif_pos b.2]
  simp_rw [hg]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun P : Pauli n × Pauli n =>
    P.1 ≠ 0 ∧ (pairSupport P).card ≤ k)) (by simp) g]
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  by_cases h : P.1 ≠ 0 ∧ (pairSupport P).card ≤ k
  · simp only [g, dif_pos h, if_pos h, ext]
    by_cases hi : i ∈ pairSupport P
    · simp [hi, h.1]
    · simp [hi]
  · simp only [g, dif_neg h, if_neg h, ext]
    split_ifs <;> simp

def ssN {k : ℕ} (y : Idx n k → ℂ) (i : Fin n) : ℝ≥0 := ⟨ss y i, ss_nonneg y i⟩

def supN {k : ℕ} (y : Idx n k → ℂ) : ℝ≥0 := Finset.univ.sup (ssN y)

lemma b1Norm_ext_eq {k : ℕ} (y : Idx n k → ℂ) : b1Norm (ext y) = (supN y : ℝ) := by
  unfold b1Norm supN
  congr 2
  funext i
  apply NNReal.eq
  rw [site_eq]
  rfl

lemma ss_le_b1 {k : ℕ} (y : Idx n k → ℂ) (i : Fin n) : ss y i ≤ b1Norm (ext y) := by
  rw [b1Norm_ext_eq]
  have : ssN y i ≤ supN y := Finset.le_sup (f := ssN y) (Finset.mem_univ i)
  exact this

lemma b1_le_of_ss {k : ℕ} (y x : Idx n k → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ i, ss y i ≤ C * ss x i) : b1Norm (ext y) ≤ C * b1Norm (ext x) := by
  rw [b1Norm_ext_eq y]
  have hb : 0 ≤ b1Norm (ext x) := by rw [b1Norm_ext_eq]; exact NNReal.coe_nonneg _
  have : supN y ≤ ⟨C * b1Norm (ext x), mul_nonneg hC hb⟩ := by
    apply Finset.sup_le
    intro i _
    show ss y i ≤ C * b1Norm (ext x)
    exact (h i).trans (mul_le_mul_of_nonneg_left (ss_le_b1 x i) hC)
  exact this

/-- the sup norm is bounded by the local one-norm -/
lemma norm_le_b1 {k : ℕ} (y : Idx n k → ℂ) : ‖y‖ ≤ b1Norm (ext y) := by
  have hb : 0 ≤ b1Norm (ext y) := by rw [b1Norm_ext_eq]; exact NNReal.coe_nonneg _
  refine (pi_norm_le_iff_of_nonneg hb).2 (fun b => ?_)
  obtain ⟨i, hi⟩ : ∃ i, i ∈ pairSupport b.1 := by
    by_contra hne
    push Not at hne
    apply b.2.1
    funext j
    exact ((not_mem_pairSupport_iff b.1 j).1 (hne j)).1
  refine le_trans ?_ (ss_le_b1 y i)
  unfold ss
  classical
  have := Finset.single_le_sum (f := fun c : Idx n k => if i ∈ pairSupport c.1 then ‖y c‖ else 0)
    (fun c _ => by split_ifs <;> simp) (Finset.mem_univ b)
  simp only [hi, if_true] at this
  convert this

open Classical in
/-- column-sum criterion -/
lemma ss_mulVec_le {k : ℕ} (M : Matrix (Idx n k) (Idx n k) ℂ) (C : ℝ)
    (hM : ∀ b : Idx n k, ∀ i : Fin n,
      ∑ a : Idx n k, (if i ∈ pairSupport a.1 then ‖M a b‖ else 0) ≤
        C * (if i ∈ pairSupport b.1 then 1 else 0))
    (x : Idx n k → ℂ) (i : Fin n) : ss (M.mulVec x) i ≤ C * ss x i := by
  unfold ss
  calc ∑ a : Idx n k, (if i ∈ pairSupport a.1 then ‖M.mulVec x a‖ else 0)
      ≤ ∑ a : Idx n k, ∑ b : Idx n k, (if i ∈ pairSupport a.1 then ‖M a b‖ * ‖x b‖ else 0) := by
        apply Finset.sum_le_sum
        intro a _
        split_ifs
        · simp only [Matrix.mulVec, dotProduct]
          refine (norm_sum_le _ _).trans ?_
          apply le_of_eq
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [norm_mul]
        · simp
    _ = ∑ b : Idx n k, ‖x b‖ * ∑ a : Idx n k, (if i ∈ pairSupport a.1 then ‖M a b‖ else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        split_ifs <;> ring
    _ ≤ ∑ b : Idx n k, ‖x b‖ * (C * (if i ∈ pairSupport b.1 then 1 else 0)) := by
        apply Finset.sum_le_sum
        intro b _
        exact mul_le_mul_of_nonneg_left (hM b i) (norm_nonneg _)
    _ = C * ∑ b : Idx n k, (if i ∈ pairSupport b.1 then ‖x b‖ else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        split_ifs <;> ring


lemma confuses_eq_mid {a b : Pauli n × Pauli n} (h : confuses b a) :
    a = mid (pairSupport a) b := by
  rw [confuses_iff] at h
  ext : 1
  · funext i; simp only [mid]
    by_cases hi : i ∈ pairSupport a
    · simp [hi, (h.1 i hi).1]
    · simp [hi, ((not_mem_pairSupport_iff a i).1 hi).1]
  · funext i; simp only [mid]
    by_cases hi : i ∈ pairSupport a
    · simp [hi, (h.1 i hi).2]
    · simp [hi, ((not_mem_pairSupport_iff a i).1 hi).2]

open Classical in
lemma count_below {k : ℕ} (b : Idx n k) (i : Fin n) :
    ∑ a : Idx n k, (if i ∈ pairSupport a.1 ∧ confuses b.1 a.1 then (1 : ℝ) else 0) ≤
      2 ^ k * (if i ∈ pairSupport b.1 then 1 else 0) := by
  rw [Finset.sum_boole]
  by_cases hi : i ∈ pairSupport b.1
  · rw [if_pos hi, mul_one]
    have hcard : (Finset.univ.filter (fun a : Idx n k => i ∈ pairSupport a.1 ∧
        confuses b.1 a.1)).card ≤ (pairSupport b.1).powerset.card := by
      apply Finset.card_le_card_of_injOn (fun a => pairSupport a.1)
      · intro a ha
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha
        simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
        exact confuses_support ha.2
      · intro a ha a' ha' e
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha ha'
        apply Subtype.ext
        rw [confuses_eq_mid ha.2, confuses_eq_mid ha'.2]
        simp only at e
        rw [e]
    rw [Finset.card_powerset] at hcard
    have h2 : (2 : ℝ) ^ (pairSupport b.1).card ≤ 2 ^ k :=
      pow_le_pow_right₀ (by norm_num) b.2.2
    calc ((Finset.univ.filter (fun a : Idx n k => i ∈ pairSupport a.1 ∧
        confuses b.1 a.1)).card : ℝ) ≤ ((2 ^ (pairSupport b.1).card : ℕ) : ℝ) := by
          exact_mod_cast hcard
      _ ≤ 2 ^ k := by push_cast; exact h2
  · rw [if_neg hi, mul_zero]
    have : Finset.univ.filter (fun a : Idx n k => i ∈ pairSupport a.1 ∧
        confuses b.1 a.1) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      rintro a - ⟨h1, h2⟩
      exact hi (confuses_support h2 h1)
    rw [this]; simp

open Classical in
lemma count_eq {k : ℕ} (b : Idx n k) (i : Fin n) (p : Pauli n × Pauli n)
    (hp : i ∈ pairSupport p → i ∈ pairSupport b.1) :
    ∑ a : Idx n k, (if i ∈ pairSupport a.1 ∧ a.1 = p then (1 : ℝ) else 0) ≤
      (if i ∈ pairSupport b.1 then 1 else 0) := by
  by_cases hi : i ∈ pairSupport p
  · rw [if_pos (hp hi)]
    calc ∑ a : Idx n k, (if i ∈ pairSupport a.1 ∧ a.1 = p then (1 : ℝ) else 0)
        ≤ ∑ a : Idx n k, (if a.1 = p then (1 : ℝ) else 0) := by
          apply Finset.sum_le_sum; intro a _
          split_ifs with h1 h2 <;> first | exact le_rfl | (exact absurd h1.2 h2) | norm_num
      _ ≤ 1 := by
          rw [Finset.sum_boole]
          have : (Finset.univ.filter (fun a : Idx n k => a.1 = p)).card ≤ 1 := by
            apply Finset.card_le_one.2
            intro a ha a' ha'
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ha'
            exact Subtype.ext (ha.trans ha'.symm)
          exact_mod_cast this
  · apply le_trans _ (by split_ifs <;> norm_num : (0 : ℝ) ≤ if i ∈ pairSupport b.1 then 1 else 0)
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro a _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hi (h2 ▸ h1)

lemma mem_W0 {k : ℕ} (b : Idx n k) (i : Fin n) :
    i ∈ pairSupport (pauliProd b.1.2 b.1.1, (0 : Pauli n)) → i ∈ pairSupport b.1 := by
  rw [pairSupport_P0, mem_support_iff, mem_pairSupport_iff]
  intro h
  by_contra h'
  push Not at h'
  apply h
  simp [pauliProd, h'.1, h'.2, letterMul_self]

lemma norm_letterPhase (a b : Fin 4) : ‖letterPhase a b‖ = 1 := by
  fin_cases a <;> fin_cases b <;> simp [letterPhase]

lemma norm_star_pauliPhase (P Q : Pauli n) : ‖star (pauliPhase P Q)‖ = 1 := by
  rw [norm_star, pauliPhase, norm_prod]
  simp [norm_letterPhase]

open Classical in
lemma norm_Amat_le {k : ℕ} (a b : Idx n k) :
    ‖Amat n k a b‖ ≤ (if confuses b.1 a.1 then (1 : ℝ) else 0) +
      (1 / 2) * (if a.1 = (pauliProd b.1.2 b.1.1, 0) then 1 else 0) := by
  rw [Amat_apply]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · split_ifs <;> simp
  · rw [norm_mul]
    have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [h12]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    by_cases h : a.1.2 = 0 ∧ pauliProd b.1.2 b.1.1 = a.1.1
    · rw [if_pos h, if_pos (Prod.ext h.2.symm h.1)]
      rw [pauliPhase, norm_prod]; simp [norm_letterPhase]
    · rw [if_neg h]; simp only [norm_zero]; split_ifs <;> norm_num

lemma restrict_of_support_sub (S : Finset (Fin n)) (Q : Pauli n) (h : support Q ⊆ S) :
    restrict S Q = Q := by
  funext i
  simp only [restrict]
  split_ifs with hi
  · rfl
  · exact ((not_mem_support_iff Q i).1 (fun hq => hi (h hq))).symm

open Classical in
lemma norm_Vmat_le {k : ℕ} (a b : Idx n k) :
    ‖Vmat n k a b‖ ≤ (if confuses b.1 a.1 then (1 : ℝ) else 0) +
      (if a = b then 1 else 0) + (if a.1 = (pauliProd b.1.2 b.1.1, 0) then 1 else 0) := by
  have hnn : ∀ (p : Prop) [Decidable p], (0 : ℝ) ≤ if p then 1 else 0 := by
    intro p _; split_ifs <;> norm_num
  by_cases ha : a.1.2 ≠ 0
  · rw [Vmat_apply_ne a b ha]
    have : ‖(if confuses b.1 a.1 then
        (-1 : ℂ) ^ ((pairSupport b.1).card - (pairSupport a.1).card) else 0)‖ ≤
        (if confuses b.1 a.1 then (1 : ℝ) else 0) := by
      split_ifs <;> simp
    linarith [hnn (a = b), hnn (a.1 = (pauliProd b.1.2 b.1.1, 0))]
  · push Not at ha
    rw [Vmat_apply_eq a b ha]
    set P := a.1.1 with hPdef
    have hP : P ≠ 0 := a.2.1
    have haP : a.1 = (P, 0) := Prod.ext rfl ha
    by_cases hab : a = b
    · subst hab
      have h2 : ¬ (support a.1.1 ⊆ support a.1.1 ∧ a.1.1 ≠ 0 ∧ a.1.1 ≠ a.1.1 ∧
          a.1.2 = pauliProd a.1.1 a.1.1) := fun h => h.2.2.1 rfl
      have h3 : ¬ (confuses a.1 a.1 ∧ a.1 ≠ a.1) := fun h => h.2 rfl
      have h4 : ¬ (confuses a.1 (0, a.1.1) ∧ a.1 ≠ (0, a.1.1)) := by
        rintro ⟨h, _⟩
        rw [confuses_0P_iff] at h
        apply hP
        rw [← h.2, restrict_of_support_sub _ _ le_rfl]
      rw [if_pos rfl, if_neg h2, if_neg h3, if_neg h4, if_pos (confuses_refl _), if_pos rfl]
      norm_num
      linarith [hnn (a.1 = (pauliProd a.1.2 a.1.1, 0))]
    · have hne : b.1 ≠ a.1 := fun e => hab (Subtype.ext e).symm
      rw [if_neg hne, zero_add]
      have hW : ∀ h : b.1.2 = pauliProd P b.1.1,
          (if a.1 = (pauliProd b.1.2 b.1.1, 0) then (1 : ℝ) else 0) = 1 := by
        intro h
        rw [if_pos]
        rw [haP]
        congr 1
        exact ((pauliProd_eq_iff _ _ _).2 h).symm
      by_cases h2 : support b.1.1 ⊆ support a.1.1 ∧ b.1.1 ≠ 0 ∧ b.1.1 ≠ a.1.1 ∧
          b.1.2 = pauliProd a.1.1 b.1.1
      · have h3 : ¬ (confuses b.1 a.1 ∧ b.1 ≠ a.1) := by
          rintro ⟨h, _⟩
          rw [haP, confuses_P0_iff, restrict_of_support_sub _ _ h2.1] at h
          exact h2.2.2.1 h.2
        have h4 : ¬ (confuses b.1 (0, a.1.1) ∧ b.1 ≠ (0, a.1.1)) := by
          rintro ⟨h, _⟩
          rw [confuses_0P_iff, restrict_of_support_sub _ _ h2.1] at h
          exact h2.2.1 h.2
        rw [if_pos h2, if_neg h3, if_neg h4, add_zero, sub_zero, norm_star_pauliPhase,
          hW h2.2.2.2]
        linarith [hnn (confuses b.1 a.1), hnn (a = b)]
      · rw [if_neg h2, zero_add]
        by_cases h3 : confuses b.1 a.1 ∧ b.1 ≠ a.1
        · have h4 : ¬ (confuses b.1 (0, a.1.1) ∧ b.1 ≠ (0, a.1.1)) := by
            rintro ⟨h, _⟩
            have h' := h3.1
            rw [haP, confuses_P0_iff] at h'
            rw [confuses_0P_iff] at h
            exact hP (h'.2.symm.trans h.2)
          have hb := h3.1
          rw [haP, confuses_P0_iff] at hb
          rw [if_pos h3, if_neg h4, sub_zero, hW hb.1, if_pos h3.1]
          simp only [norm_pow, norm_neg, norm_one, one_pow]
          linarith [hnn (a = b)]
        · rw [if_neg h3, zero_sub, norm_neg]
          by_cases h4 : confuses b.1 (0, a.1.1) ∧ b.1 ≠ (0, a.1.1)
          · have hb := h4.1
            rw [confuses_0P_iff] at hb
            rw [if_pos h4, hW hb.1]
            simp only [norm_pow, norm_neg, norm_one, one_pow]
            linarith [hnn (confuses b.1 a.1), hnn (a = b)]
          · rw [if_neg h4, norm_zero]
            linarith [hnn (confuses b.1 a.1), hnn (a.1 = (pauliProd b.1.2 b.1.1, 0)), hnn (a = b)]


open Classical in
lemma col_bound {k : ℕ} (M : Matrix (Idx n k) (Idx n k) ℂ)
    (hM : ∀ a b : Idx n k, ‖M a b‖ ≤ (if confuses b.1 a.1 then (1 : ℝ) else 0) +
      (if a = b then 1 else 0) + (if a.1 = (pauliProd b.1.2 b.1.1, 0) then 1 else 0))
    (b : Idx n k) (i : Fin n) :
    ∑ a : Idx n k, (if i ∈ pairSupport a.1 then ‖M a b‖ else 0) ≤
      (2 ^ k + 2) * (if i ∈ pairSupport b.1 then 1 else 0) := by
  calc ∑ a : Idx n k, (if i ∈ pairSupport a.1 then ‖M a b‖ else 0)
      ≤ ∑ a : Idx n k, ((if i ∈ pairSupport a.1 ∧ confuses b.1 a.1 then (1 : ℝ) else 0) +
          (if a = b then (if i ∈ pairSupport b.1 then 1 else 0) else 0) +
          (if i ∈ pairSupport a.1 ∧ a.1 = (pauliProd b.1.2 b.1.1, 0) then 1 else 0)) := by
        apply Finset.sum_le_sum
        intro a _
        by_cases hi : i ∈ pairSupport a.1
        · rw [if_pos hi]
          refine (hM a b).trans (le_of_eq ?_)
          by_cases hab : a = b
          · subst hab; simp [hi]
          · simp [hi, hab]
        · rw [if_neg hi]
          have : ¬ (a = b ∧ i ∈ pairSupport b.1) := fun h => hi (h.1 ▸ h.2)
          apply add_nonneg (add_nonneg (by simp [hi]) ?_) (by simp [hi])
          split_ifs <;> norm_num
    _ = ∑ a : Idx n k, (if i ∈ pairSupport a.1 ∧ confuses b.1 a.1 then (1 : ℝ) else 0) +
        (if i ∈ pairSupport b.1 then 1 else 0) +
        ∑ a : Idx n k, (if i ∈ pairSupport a.1 ∧ a.1 = (pauliProd b.1.2 b.1.1, 0) then 1 else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp
    _ ≤ 2 ^ k * (if i ∈ pairSupport b.1 then 1 else 0) + (if i ∈ pairSupport b.1 then 1 else 0) +
        (if i ∈ pairSupport b.1 then 1 else 0) := by
        gcongr
        · exact count_below b i
        · exact count_eq b i _ (mem_W0 b i)
    _ = (2 ^ k + 2) * (if i ∈ pairSupport b.1 then 1 else 0) := by ring

open Classical in
lemma b1_mulVec_le {k : ℕ} (M : Matrix (Idx n k) (Idx n k) ℂ)
    (hM : ∀ a b : Idx n k, ‖M a b‖ ≤ (if confuses b.1 a.1 then (1 : ℝ) else 0) +
      (if a = b then 1 else 0) + (if a.1 = (pauliProd b.1.2 b.1.1, 0) then 1 else 0))
    (x : Idx n k → ℂ) : b1Norm (ext (M.mulVec x)) ≤ 4 ^ k * b1Norm (ext x) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hempty : IsEmpty (Idx n 0) := ⟨fun b => b.2.1 (by
      funext i
      have := b.2.2
      rw [Nat.le_zero, Finset.card_eq_zero] at this
      have hi : i ∉ pairSupport b.1 := by rw [this]; simp
      exact ((not_mem_pairSupport_iff b.1 i).1 hi).1)⟩
    have h0 : ∀ y : Idx n 0 → ℂ, b1Norm (ext y) = 0 := by
      intro y
      rw [b1Norm_ext_eq]
      have : supN y = 0 := by
        unfold supN
        apply le_antisymm _ (zero_le')
        apply Finset.sup_le
        intro i _
        show ss y i ≤ 0
        unfold ss
        simp
      rw [this]; rfl
    rw [h0, h0]; simp
  · have hC : (2 : ℝ) ^ k + 2 ≤ 4 ^ k := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      have : (4 : ℝ) ^ (j + 1) = 2 ^ (j + 1) * 2 ^ (j + 1) := by
        rw [← mul_pow]; norm_num
      rw [this, pow_succ]
      nlinarith
    have hb : 0 ≤ b1Norm (ext x) := by rw [b1Norm_ext_eq]; exact NNReal.coe_nonneg _
    refine (b1_le_of_ss _ x (2 ^ k + 2) (by positivity)
      (ss_mulVec_le M _ (col_bound M hM) x)).trans ?_
    exact mul_le_mul_of_nonneg_right hC hb

open Classical in
theorem lemma_3_8_aux (n k : ℕ) (x : Idx n k → ℂ) :
    (‖Matrix.mulVec (Amat n k) x‖ ≤ b1Norm (ext (Matrix.mulVec (Amat n k) x)) ∧
      b1Norm (ext (Matrix.mulVec (Amat n k) x)) ≤ 4 ^ k * b1Norm (ext x)) ∧
    (‖Matrix.mulVec (Amat n k)⁻¹ x‖ ≤ b1Norm (ext (Matrix.mulVec (Amat n k)⁻¹ x)) ∧
      b1Norm (ext (Matrix.mulVec (Amat n k)⁻¹ x)) ≤ 4 ^ k * b1Norm (ext x)) := by
  classical
  have hinv : (Amat n k)⁻¹ = Vmat n k := Matrix.inv_eq_left_inv (VA_one k)
  refine ⟨⟨norm_le_b1 _, b1_mulVec_le _ ?_ x⟩, ⟨norm_le_b1 _, ?_⟩⟩
  · intro a b
    refine (norm_Amat_le a b).trans ?_
    have h1 : (0 : ℝ) ≤ if a = b then 1 else 0 := by split_ifs <;> norm_num
    have h2 : (1 / 2 : ℝ) * (if a.1 = (pauliProd b.1.2 b.1.1, 0) then 1 else 0) ≤
        (if a.1 = (pauliProd b.1.2 b.1.1, 0) then 1 else 0) := by split_ifs <;> norm_num
    linarith
  · rw [hinv]
    exact b1_mulVec_le _ norm_Vmat_le x

end LindbladStructLearn.AAux


namespace LindbladStructLearn.AAux
open LindbladTolerant.Testing LindbladStructLearn LindbladStructLearn.FourierAux

variable {n : ℕ}

lemma sum_tens (F : Fin n → Bool → Op Bool) :
    ∑ w : Qubits n, tens (fun i => F i (w i)) = tens (fun i => ∑ b, F i b) := by
  ext x y
  simp only [tens, Matrix.sum_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

lemma eigenProj_eq (A : Pauli n) (v : Qubits n) :
    eigenProj A v = tens (fun i => oneEigenProj (A i) (v i)) := rfl

lemma boolChar_eq (S : Finset (Fin n)) (v : Qubits n) :
    boolChar S v = ∏ i, (if i ∈ S then (if v i then (-1 : ℂ) else 1) else 1) := by
  rw [boolChar, Finset.prod_ite_mem, Finset.univ_inter]

lemma one_eigen_sum (a : Fin 4) :
    ∑ b : Bool, oneEigenProj a b = 1 := by
  ext x y
  fin_cases a <;> cases x <;> cases y <;>
    simp [oneEigenProj, onePauli, Fintype.sum_bool] <;> norm_num

lemma one_eigen_signed (a : Fin 4) (ha : a ≠ 0) :
    ∑ b : Bool, (if b then (-1 : ℂ) else 1) • oneEigenProj a b = onePauli a := by
  ext x y
  fin_cases a <;> cases x <;> cases y <;>
    simp_all [oneEigenProj, onePauli, Fintype.sum_bool] <;> ring

/-- eigendecomposition: `Σ_w χ_{S_Z}(w) |B,w⟩⟨B,w| = Z` for `Z = B^S` -/
lemma eigen_decomp (S : Finset (Fin n)) (B : Pauli n) :
    ∑ w : Qubits n, boolChar (support (restrict S B)) w • eigenProj B w =
      pauliMatrix (restrict S B) := by
  simp_rw [boolChar_eq, eigenProj_eq, ← tens_smul]
  rw [sum_tens (fun i b => (if i ∈ support (restrict S B) then (if b = true then (-1 : ℂ) else 1)
    else 1) • oneEigenProj (B i) b), pauliMatrix_eq_tens]
  congr 1
  funext i
  by_cases hi : i ∈ support (restrict S B)
  · simp only [hi, if_true]
    have hz : restrict S B i ≠ 0 := (mem_support_iff _ _).1 hi
    have hB : restrict S B i = B i := by
      simp only [restrict] at hz ⊢; split_ifs at hz ⊢ with h; rfl; exact absurd rfl hz
    rw [hB] at hz ⊢
    exact one_eigen_signed _ hz
  · simp only [hi, if_false, one_smul]
    rw [(not_mem_support_iff _ _).1 hi, one_eigen_sum, onePauli_zero]

lemma applySuper_add_right (g : Super (Qubits n) (Qubits n)) (X Y : Op (Qubits n)) :
    applySuper g (X + Y) = applySuper g X + applySuper g Y := by
  ext i j
  simp only [applySuper, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

lemma applySuper_smul_right (g : Super (Qubits n) (Qubits n)) (c : ℂ) (X : Op (Qubits n)) :
    applySuper g (c • X) = c • applySuper g X := by
  ext i j
  simp only [applySuper, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => ?_))
  ring

lemma applySuper_sum_smul {ι : Type*} (s : Finset ι) (g : Super (Qubits n) (Qubits n))
    (c : ι → ℂ) (X : ι → Op (Qubits n)) :
    applySuper g (∑ v ∈ s, c v • X v) = ∑ v ∈ s, c v • applySuper g (X v) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext i j; simp [applySuper]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, applySuper_add_right, applySuper_smul_right, ih]

/-- sum of `bornAmp` against the two characters -/
lemma born_sum (Φ : Super (Qubits n) (Qubits n)) (S : Finset (Fin n)) (A B : Pauli n) :
    ∑ v : Qubits n, ∑ w : Qubits n, bornAmp Φ A v B w *
      (boolChar (support (restrict S A)) v * boolChar (support (restrict S B)) w) =
      (pauliMatrix (restrict S B) * applySuper Φ (pauliMatrix (restrict S A))).trace := by
  rw [← eigen_decomp S A, ← eigen_decomp S B, applySuper_sum_smul]
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul]
  refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun w _ => ?_))
  rw [bornAmp]
  ring

/-- fibres of the restriction map -/
lemma card_restrict_fibre (S : Finset (Fin n)) (R : Pauli n) (hR : R ∈ paulisOn S) :
    (Finset.univ.filter (fun A : Pauli n => restrict S A = R)).card = 4 ^ (n - S.card) := by
  have hR' : ∀ i, i ∉ S → R i = 0 := by
    intro i hi
    simp only [paulisOn, Finset.mem_filter, Finset.mem_univ, true_and] at hR
    by_contra h
    exact hi (hR ((mem_support_iff R i).2 h))
  have : Finset.univ.filter (fun A : Pauli n => restrict S A = R) =
      Fintype.piFinset (fun i => if i ∈ S then {R i} else (Finset.univ : Finset (Fin 4))) := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, funext_iff,
      restrict]
    constructor
    · intro h i
      by_cases hi : i ∈ S
      · have := h i; simp only [hi, if_true] at this; simp [hi, this]
      · simp [hi]
    · intro h i
      by_cases hi : i ∈ S
      · have := h i; simp only [hi, if_true, Finset.mem_singleton] at this; simp [hi, this]
      · simp [hi, hR' i hi]
  rw [this, Fintype.card_piFinset]
  have : ∀ i, ((if i ∈ S then {R i} else (Finset.univ : Finset (Fin 4))) : Finset (Fin 4)).card =
      if i ∈ S then 1 else 4 := by
    intro i; split_ifs <;> simp
  simp_rw [this]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
  simp

lemma sum_restrict (S : Finset (Fin n)) (f : Pauli n → ℂ) :
    ∑ A : Pauli n, f (restrict S A) = (4 : ℂ) ^ (n - S.card) * ∑ R ∈ paulisOn S, f R := by
  classical
  have hmem : ∀ A : Pauli n, restrict S A ∈ paulisOn S := by
    intro A
    simp only [paulisOn, Finset.mem_filter, Finset.mem_univ, true_and]
    exact restrict_support_sub S A
  rw [← Finset.sum_fiberwise_of_maps_to (fun A _ => hmem A)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun R hR => ?_)
  rw [Finset.sum_congr rfl (fun A hA => by rw [(Finset.mem_filter.1 hA).2]),
    Finset.sum_const, card_restrict_fibre S R hR]
  simp


lemma pauliMatrix_conjTranspose (P : Pauli n) : (pauliMatrix P)ᴴ = pauliMatrix P := by
  rw [pauliMatrix_eq_tens, tens_conjTranspose]
  simp_rw [onePauli_conjTranspose]

lemma mem_paulisOn_restrict (S : Finset (Fin n)) (A : Pauli n) : restrict S A ∈ paulisOn S := by
  simp only [paulisOn, Finset.mem_filter, Finset.mem_univ, true_and]
  exact restrict_support_sub S A

lemma pauliProd_mem (S : Finset (Fin n)) (P Q : Pauli n) (hP : support P ⊆ S) (hQ : support Q ⊆ S) :
    support (pauliProd P Q) ⊆ S := by
  intro i hi
  rw [mem_support_iff] at hi
  by_contra h
  apply hi
  have h1 := (not_mem_support_iff P i).1 (fun x => h (hP x))
  have h2 := (not_mem_support_iff Q i).1 (fun x => h (hQ x))
  simp [pauliProd, h1, h2, letterMul_self]

open Classical in
theorem proposition_2_9_aux (Φ : Super (Qubits n) (Qubits n)) (P : Pauli n × Pauli n) :
    ∑ A : Pauli n, ∑ v : Qubits n, ∑ B : Pauli n, ∑ w : Qubits n,
      ((1 / 4 ^ n : ℂ) * (1 / 2 ^ n) * (1 / 4 ^ n)) * bornAmp Φ A v B w * alg1Sample P A v B w =
      locFourier Φ P := by
  set S := pairSupport P with hS
  have hP1 : support P.1 ⊆ S := Finset.subset_union_left
  have hP2 : support P.2 ⊆ S := Finset.subset_union_right
  set c0 : ℂ := (1 / 4 ^ n : ℂ) * (1 / 2 ^ n) * (1 / 4 ^ n) with hc0
  set W : Pauli n → Pauli n := fun R => pauliProd (pauliProd P.2 R) P.1 with hW
  set g : Pauli n → ℂ := fun R =>
    (pauliMatrix P.2 * pauliMatrix R * pauliMatrix P.1 * applySuper Φ (pauliMatrix R)).trace with hg
  -- step 1+2+3: inner sums
  have inner : ∀ A B : Pauli n, ∑ v : Qubits n, ∑ w : Qubits n,
      c0 * bornAmp Φ A v B w * alg1Sample P A v B w =
      c0 * (4 : ℂ) ^ S.card * ((if restrict S B = W (restrict S A) then 1 else 0) *
        g (restrict S A)) := by
    intro A B
    by_cases hZ : restrict S B = W (restrict S A)
    · have hsamp : ∀ v w, alg1Sample P A v B w = (4 : ℂ) ^ S.card *
          (pauliPhase P.2 (restrict S A) * pauliPhase (pauliProd P.2 (restrict S A)) P.1) *
          (boolChar (support (restrict S A)) v * boolChar (support (restrict S B)) w) := by
        intro v w
        simp only [alg1Sample]
        rw [if_pos hZ]
        ring
      simp_rw [hsamp]
      have : ∀ v w, c0 * bornAmp Φ A v B w * ((4 : ℂ) ^ S.card *
          (pauliPhase P.2 (restrict S A) * pauliPhase (pauliProd P.2 (restrict S A)) P.1) *
          (boolChar (support (restrict S A)) v * boolChar (support (restrict S B)) w)) =
          (c0 * (4 : ℂ) ^ S.card *
          (pauliPhase P.2 (restrict S A) * pauliPhase (pauliProd P.2 (restrict S A)) P.1)) *
          (bornAmp Φ A v B w * (boolChar (support (restrict S A)) v *
            boolChar (support (restrict S B)) w)) := by intro v w; ring
      simp_rw [this, ← Finset.mul_sum]
      rw [born_sum, if_pos hZ, one_mul, hZ]
      simp only [hg, hW]
      have hm : pauliMatrix P.2 * pauliMatrix (restrict S A) * pauliMatrix P.1 =
          (pauliPhase P.2 (restrict S A) * pauliPhase (pauliProd P.2 (restrict S A)) P.1) •
            pauliMatrix (pauliProd (pauliProd P.2 (restrict S A)) P.1) := by
        rw [pauliMatrix_mul P.2, Matrix.smul_mul, pauliMatrix_mul, smul_smul]
      rw [hm, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      ring
    · have hsamp : ∀ v w, alg1Sample P A v B w = 0 := by
        intro v w; simp only [alg1Sample]; rw [if_neg hZ]
      simp [hsamp, hZ]
  rw [Finset.sum_congr rfl (fun A _ => by rw [Finset.sum_comm])]
  simp_rw [inner]
  -- sum over B
  have hB : ∀ A : Pauli n, ∑ B : Pauli n, c0 * (4 : ℂ) ^ S.card *
      ((if restrict S B = W (restrict S A) then 1 else 0) * g (restrict S A)) =
      c0 * (4 : ℂ) ^ S.card * ((4 : ℂ) ^ (n - S.card) * g (restrict S A)) := by
    intro A
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    congr 2
    rw [sum_restrict S (fun Z => if Z = W (restrict S A) then (1 : ℂ) else 0)]
    rw [Finset.sum_ite_eq', if_pos]
    · ring
    · simp only [paulisOn, Finset.mem_filter, Finset.mem_univ, true_and, hW]
      exact pauliProd_mem S _ _ (pauliProd_mem S _ _ hP2 (restrict_support_sub S A)) hP1
  simp_rw [hB]
  rw [← Finset.mul_sum, ← Finset.mul_sum,
    sum_restrict S (fun R => g R)]
  -- the local Fourier coefficient
  have hloc : locFourier Φ P = (∑ R ∈ paulisOn S, g R) / (2 : ℂ) ^ n / (4 : ℂ) ^ S.card := by
    unfold locFourier pauliAvg
    rw [← hS]
    congr 1
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun R _ => ?_)
    simp only [ntr, chi, hg, Matrix.conjTranspose_mul, pauliMatrix_conjTranspose, Matrix.mul_assoc]
  rw [hloc, hc0]
  have hsn : S.card ≤ n := by
    calc S.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  have h4 : (4 : ℂ) ^ (n - S.card) * (4 : ℂ) ^ S.card = 4 ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hsn]
  have h4ne : (4 : ℂ) ^ S.card ≠ 0 := pow_ne_zero _ (by norm_num)
  have h4n : (4 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2n : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  have h4' : (4 : ℂ) ^ (S.card * 2) * 4 ^ ((n - S.card) * 2) = 4 ^ (n * 2) := by
    rw [← pow_add]; congr 1; omega
  linear_combination (∑ R ∈ paulisOn S, g R) * h4'

end LindbladStructLearn.AAux


namespace LindbladStructLearn.AAux
open LindbladTolerant.Testing LindbladStructLearn LindbladStructLearn.FourierAux

variable {n : ℕ}

lemma mem_bind {α β : Type*} (μ : FinDist α) (f : α → FinDist β) (o : ℝ × β) :
    o ∈ FinDist.bind μ f ↔ ∃ pa ∈ μ, ∃ qb ∈ f pa.2, o = (pa.1 * qb.1, qb.2) := by
  unfold FinDist.bind
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨pa, hpa, qb, hqb, rfl⟩; exact ⟨pa, hpa, qb, hqb, rfl⟩
  · rintro ⟨pa, hpa, qb, hqb, rfl⟩; exact ⟨pa, hpa, qb, hqb, rfl⟩

lemma list_sum_smul {γ M : Type*} [AddCommMonoid M] [Module ℂ M] (l : List γ) (c : ℂ)
    (F : γ → M) : (l.map (fun b => c • F b)).sum = c • (l.map F).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, smul_add]

lemma expect_bind {α β : Type*} (μ : FinDist α) (f : α → FinDist β) (g : β → ℂ) :
    FinDist.expect (FinDist.bind μ f) g =
      (μ.map (fun pa => (pa.1 : ℂ) * FinDist.expect (f pa.2) g)).sum := by
  induction μ with
  | nil => simp [FinDist.bind, FinDist.expect]
  | cons pa μ ih =>
    have h1 : FinDist.expect (FinDist.bind (pa :: μ) f) g =
        FinDist.expect ((f pa.2).map (fun qb => (pa.1 * qb.1, qb.2))) g +
          FinDist.expect (FinDist.bind μ f) g := by
      simp [FinDist.bind, FinDist.expect]
    rw [h1, ih]
    simp only [List.map_cons, List.sum_cons]
    congr 1
    simp only [FinDist.expect, List.map_map, Function.comp_def]
    have := list_sum_smul (f pa.2) (pa.1 : ℂ) (fun b => (b.1 : ℂ) * g b.2)
    simp only [smul_eq_mul] at this
    rw [← this]
    congr 1
    apply List.map_congr_left
    intro qb _
    push_cast; ring

lemma expect_map {α β : Type*} (μ : FinDist α) (h : α → β) (g : β → ℂ) :
    FinDist.expect (μ.map (fun pa => (pa.1, h pa.2))) g = FinDist.expect μ (g ∘ h) := by
  simp only [FinDist.expect, List.map_map, Function.comp_def]

lemma expect_uniform {α : Type*} (s : Finset α) (g : α → ℂ) :
    FinDist.expect (FinDist.uniform s) g = (∑ a ∈ s, g a) / (s.card : ℂ) := by
  unfold FinDist.expect FinDist.uniform
  rw [List.map_map]
  have : ((fun pa : ℝ × α => (pa.1 : ℂ) * g pa.2) ∘ fun a => ((s.card : ℝ)⁻¹, a)) =
      fun a => ((s.card : ℂ))⁻¹ * g a := by
    funext a; simp
  rw [this, Finset.sum_map_toList, Finset.sum_div]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [div_eq_inv_mul]

/-- matrix-valued expectation of `c · Q` over a law of Algorithm-2 states -/
def MExp (μ : FinDist (ℂ × Pauli n × Finset (Fin n))) : Op (Qubits n) :=
  (μ.map (fun o => ((o.1 : ℂ) * o.2.1) • pauliMatrix o.2.2.1)).sum

lemma MExp_bind (μ : FinDist (ℂ × Pauli n × Finset (Fin n)))
    (f : ℂ × Pauli n × Finset (Fin n) → FinDist (ℂ × Pauli n × Finset (Fin n))) :
    MExp (FinDist.bind μ f) = (μ.map (fun pa => (pa.1 : ℂ) • MExp (f pa.2))).sum := by
  induction μ with
  | nil => simp [FinDist.bind, MExp]
  | cons pa μ ih =>
    have h1 : MExp (FinDist.bind (pa :: μ) f) =
        MExp ((f pa.2).map (fun qb => (pa.1 * qb.1, qb.2))) + MExp (FinDist.bind μ f) := by
      simp [FinDist.bind, MExp]
    rw [h1, ih]
    simp only [List.map_cons, List.sum_cons]
    congr 1
    simp only [MExp, List.map_map, Function.comp_def]
    rw [← list_sum_smul]
    congr 1
    apply List.map_congr_left
    intro qb _
    rw [smul_smul]; push_cast; ring_nf


lemma sum_Idx_gen {k : ℕ} {M : Type*} [AddCommMonoid M] (f : Pauli n × Pauli n → M)
    (hf : ∀ P : Pauli n × Pauli n, ¬ (P.1 ≠ 0 ∧ (pairSupport P).card ≤ k) → f P = 0) :
    ∑ b : Idx n k, f b.1 = ∑ P, f P := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun P : Pauli n × Pauli n =>
    P.1 ≠ 0 ∧ (pairSupport P).card ≤ k)) (by simp) f]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro P _ hP
  apply hf
  simpa using hP

/-- adjoint single-term superoperator -/
def termAdj (b : Pauli n × Pauli n) : Super (Qubits n) (Qubits n) :=
  leftRight (pauliMatrix b.2) (pauliMatrix b.1) -
      (1 / 2 : ℂ) • (leftRight (pauliMatrix b.2 * pauliMatrix b.1) 1 +
        leftRight 1 (pauliMatrix b.2 * pauliMatrix b.1))

lemma lindbladAdj_eq (x : Pauli n × Pauli n → ℂ) :
    lindbladAdj x = ∑ P ∈ Finset.univ.filter (fun P : Pauli n × Pauli n => P.1 ≠ 0),
      x P • termAdj P := rfl

lemma letterMul_comm (a b : Fin 4) : letterMul a b = letterMul b a := by
  fin_cases a <;> fin_cases b <;> rfl

lemma letterMul_assoc (a b c : Fin 4) : letterMul (letterMul a b) c = letterMul a (letterMul b c) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl

lemma applySuper_termAdj (b : Pauli n × Pauli n) (Q : Pauli n) :
    applySuper (termAdj b) (pauliMatrix Q) = adjTermCoeff b Q • pauliMatrix (adjTermPauli b Q) := by
  have e1 : pauliProd (pauliProd b.2 b.1) Q = pauliProd (pauliProd b.2 Q) b.1 := by
    funext i; simp only [pauliProd]
    rw [letterMul_assoc, letterMul_comm (b.1 i), ← letterMul_assoc]
  have e2 : pauliProd (pauliProd Q b.2) b.1 = pauliProd (pauliProd b.2 Q) b.1 := by
    funext i; simp only [pauliProd]; rw [letterMul_comm (Q i)]
  rw [termAdj, applySuper_sub, applySuper_smul, applySuper_add, applySuper_leftRight,
    applySuper_leftRight, applySuper_leftRight]
  simp only [Matrix.mul_one, Matrix.one_mul]
  rw [← Matrix.mul_assoc (pauliMatrix Q)]
  rw [pauliMatrix_mul b.2 Q, pauliMatrix_mul b.2 b.1, pauliMatrix_mul Q b.2]
  simp only [Matrix.smul_mul]
  rw [pauliMatrix_mul (pauliProd b.2 Q) b.1, pauliMatrix_mul (pauliProd b.2 b.1) Q,
    pauliMatrix_mul (pauliProd Q b.2) b.1, e1, e2]
  simp only [adjTermCoeff, adjTermPauli, smul_smul, ← sub_smul, ← add_smul, smul_add]

lemma adjTermCoeff_disjoint (b : Pauli n × Pauli n) (Q : Pauli n)
    (h : Disjoint (support Q) (pairSupport b)) : adjTermCoeff b Q = 0 := by
  have hs : ∀ i, Q i = 0 ∨ (b.1 i = 0 ∧ b.2 i = 0) := by
    intro i
    by_cases hq : Q i = 0
    · exact Or.inl hq
    · right
      have hi : i ∈ support Q := (mem_support_iff Q i).2 hq
      have : i ∉ pairSupport b := Finset.disjoint_left.1 h hi
      exact (not_mem_pairSupport_iff b i).1 this
  have p1 : pauliPhase b.2 Q * pauliPhase (pauliProd b.2 Q) b.1 = pauliPhase b.2 b.1 := by
    unfold pauliPhase; rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rcases hs i with hq | ⟨h1, h2⟩
    · simp [hq, pauliProd, letterMul_zero_right, letterPhase_zero_right]
    · simp [h1, h2, pauliProd, letterMul_zero_left, letterPhase_zero_left, letterPhase_zero_right]
  have p2 : pauliPhase b.2 b.1 * pauliPhase (pauliProd b.2 b.1) Q = pauliPhase b.2 b.1 := by
    unfold pauliPhase; rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rcases hs i with hq | ⟨h1, h2⟩
    · simp [hq, letterPhase_zero_right]
    · simp [h1, h2, pauliProd, letterMul_zero_left, letterPhase_zero_left, letterPhase_zero_right]
  have p3 : pauliPhase Q b.2 * pauliPhase (pauliProd Q b.2) b.1 = pauliPhase b.2 b.1 := by
    unfold pauliPhase; rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rcases hs i with hq | ⟨h1, h2⟩
    · simp [hq, pauliProd, letterMul_zero_left, letterPhase_zero_left]
    · simp [h1, h2, pauliProd, letterMul_zero_right, letterPhase_zero_left, letterPhase_zero_right]
  rw [adjTermCoeff, p1, p2, p3]
  ring


lemma ext_Idx {k : ℕ} (x : Idx n k → ℂ) (b : Idx n k) : ext x b.1 = x b := by
  unfold ext; rw [dif_pos b.2]

lemma applySuper_adj {k : ℕ} (x : Idx n k → ℂ) (Q : Pauli n) :
    applySuper (lindbladAdj (ext x)) (pauliMatrix Q) =
      ∑ b : Idx n k, (x b * adjTermCoeff b.1 Q) • pauliMatrix (adjTermPauli b.1 Q) := by
  classical
  rw [lindbladAdj_eq, applySuper_sum]
  simp_rw [applySuper_smul, applySuper_termAdj, smul_smul]
  rw [Finset.sum_filter]
  rw [← sum_Idx_gen (k := k) (fun P => if P.1 ≠ 0 then
    (ext x P * adjTermCoeff P Q) • pauliMatrix (adjTermPauli P Q) else 0)]
  · refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [if_pos b.2.1, ext_Idx]
  · intro P hP
    by_cases h1 : P.1 ≠ 0
    · rw [if_pos h1]
      have : ext x P = 0 := by unfold ext; rw [dif_neg hP]
      rw [this, zero_mul, zero_smul]
    · rw [if_neg h1]

lemma alg2Weight_nonneg {k : ℕ} (x : Idx n k → ℂ) (i : Fin n) : 0 ≤ alg2Weight x i :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

lemma norm_le_alg2Weight {k : ℕ} (x : Idx n k → ℂ) (i : Fin n) (b : Idx n k)
    (hb : i ∈ pairSupport b.1) : ‖x b‖ ≤ alg2Weight x i := by
  unfold alg2Weight
  exact Finset.single_le_sum (f := fun b => ‖x b‖) (fun _ _ => norm_nonneg _)
    (by simp [hb])

open Classical in
lemma MExp_step {k : ℕ} (x : Idx n k → ℂ) (s : ℂ × Pauli n × Finset (Fin n))
    (hs : support s.2.1 ⊆ s.2.2) :
    MExp (alg2Step x s) = s.1 • applySuper (lindbladAdj (ext x)) (pauliMatrix s.2.1) := by
  obtain ⟨c, Q, A⟩ := s
  simp only at hs ⊢
  rw [applySuper_adj]
  -- terms disjoint from `A` vanish
  have hdisj : ∀ b : Idx n k, Disjoint A (pairSupport b.1) → adjTermCoeff b.1 Q = 0 := by
    intro b hb
    exact adjTermCoeff_disjoint _ _ (Finset.disjoint_of_subset_left hs hb)
  unfold alg2Step
  simp only
  split_ifs with hW
  · simp only [MExp, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Complex.ofReal_one, one_mul, zero_smul]
    rcases hW with hW | hc
    · have hw0 : ∀ j ∈ A, alg2Weight x j = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => alg2Weight_nonneg x j)).1 hW
      rw [Finset.smul_sum]
      symm
      apply Finset.sum_eq_zero
      intro b _
      by_cases hd : Disjoint A (pairSupport b.1)
      · rw [hdisj b hd]; simp
      · obtain ⟨i, hiA, hib⟩ := Finset.not_disjoint_iff.1 hd
        have := norm_le_alg2Weight x i b hib
        rw [hw0 i hiA] at this
        have hx : x b = 0 := norm_le_zero_iff.1 this
        rw [hx]; simp
    · rw [hc]; simp
  · push Not at hW
    obtain ⟨hW0, hc0⟩ := hW
    set W : ℝ := ∑ j ∈ A, alg2Weight x j with hWdef
    have hWpos : 0 < W := lt_of_le_of_ne (Finset.sum_nonneg
      (fun j _ => alg2Weight_nonneg x j)) (Ne.symm hW0)
    simp only [MExp, List.map_map, Function.comp_def]
    rw [Finset.sum_map_toList]
    -- simplify each summand
    have hterm : ∀ ib ∈ (A ×ˢ (Finset.univ : Finset (Idx n k))).filter
        (fun ib => ib.1 ∈ pairSupport ib.2.1 ∧ x ib.2 ≠ 0),
        ((((alg2Weight x ib.1 / W * (‖x ib.2‖ / alg2Weight x ib.1) : ℝ)) : ℂ) *
          (c * ((W : ℂ) / ((A ∩ pairSupport ib.2.1).card : ℂ)) * (x ib.2 / (‖x ib.2‖ : ℂ)) *
            adjTermCoeff ib.2.1 Q)) • pauliMatrix (adjTermPauli ib.2.1 Q) =
        (1 / ((A ∩ pairSupport ib.2.1).card : ℂ)) •
          ((c * (x ib.2 * adjTermCoeff ib.2.1 Q)) • pauliMatrix (adjTermPauli ib.2.1 Q)) := by
      intro ib hib
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hib
      obtain ⟨hiA, hib1, hx⟩ := hib
      have hxn : (‖x ib.2‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hx
      have hwi : alg2Weight x ib.1 ≠ 0 :=
        ne_of_gt (lt_of_lt_of_le (norm_pos_iff.2 hx) (norm_le_alg2Weight x ib.1 ib.2 hib1))
      have hcard : ((A ∩ pairSupport ib.2.1).card : ℂ) ≠ 0 := by
        have : 0 < (A ∩ pairSupport ib.2.1).card :=
          Finset.card_pos.2 ⟨ib.1, Finset.mem_inter.2 ⟨hiA, hib1⟩⟩
        exact_mod_cast this.ne'
      rw [smul_smul]
      congr 1
      have hWc : (W : ℂ) ≠ 0 := by exact_mod_cast hW0
      have hxc : ((‖x ib.2‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hxn
      have hwc : ((alg2Weight x ib.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hwi
      push_cast
      field_simp
    rw [Finset.sum_congr rfl hterm]
    rw [Finset.sum_filter, Finset.sum_product_right, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [← Finset.sum_filter]
    by_cases hx : x b = 0
    · dsimp only
      rw [Finset.filter_false_of_mem (fun i _ h => h.2 hx)]
      simp [hx]
    · dsimp only
      rw [Finset.sum_const, smul_smul]
      have hf : A.filter (fun i => i ∈ pairSupport b.1 ∧ x b ≠ 0) = A ∩ pairSupport b.1 := by
        ext i; simp [hx]
      rw [hf]
      by_cases hd : Disjoint A (pairSupport b.1)
      · rw [hdisj b hd]; simp
      · have hcard : ((A ∩ pairSupport b.1).card : ℂ) ≠ 0 := by
          have : 0 < (A ∩ pairSupport b.1).card := by
            obtain ⟨i, hiA, hib⟩ := Finset.not_disjoint_iff.1 hd
            exact Finset.card_pos.2 ⟨i, Finset.mem_inter.2 ⟨hiA, hib⟩⟩
          exact_mod_cast this.ne'
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
        congr 1
        field_simp


lemma support_pauliProd (P Q : Pauli n) : support (pauliProd P Q) ⊆ support P ∪ support Q := by
  intro i hi
  rw [mem_support_iff] at hi
  rw [Finset.mem_union, mem_support_iff, mem_support_iff]
  by_contra h
  push Not at h
  apply hi
  simp [pauliProd, h.1, h.2, letterMul_self]

lemma support_adjTermPauli (b : Pauli n × Pauli n) (Q : Pauli n) :
    support (adjTermPauli b Q) ⊆ support Q ∪ pairSupport b := by
  intro i hi
  have h1 := support_pauliProd _ _ hi
  rw [Finset.mem_union] at h1 ⊢
  rcases h1 with h1 | h1
  · have h2 := support_pauliProd _ _ h1
    rw [Finset.mem_union] at h2
    rcases h2 with h2 | h2
    · right; exact Finset.mem_union_right _ h2
    · left; exact h2
  · right; exact Finset.mem_union_left _ h1

lemma mem_step {k : ℕ} (x : Idx n k → ℂ) (s : ℂ × Pauli n × Finset (Fin n))
    (o : ℝ × ℂ × Pauli n × Finset (Fin n)) (ho : o ∈ alg2Step x s) :
    (o = ((1 : ℝ), ((0 : ℂ), s.2.1, s.2.2))) ∨ ∃ i ∈ s.2.2, ∃ b : Idx n k, i ∈ pairSupport b.1 ∧ x b ≠ 0 ∧
      o.2 = ((s.1 * (((∑ j ∈ s.2.2, alg2Weight x j : ℝ) : ℂ) /
          ((s.2.2 ∩ pairSupport b.1).card : ℂ)) * (x b / (‖x b‖ : ℂ)) * adjTermCoeff b.1 s.2.1),
        adjTermPauli b.1 s.2.1, s.2.2 ∪ pairSupport b.1) := by
  classical
  unfold alg2Step at ho
  simp only at ho
  split_ifs at ho with hW
  · left; simpa using ho
  · right
    rw [List.mem_map] at ho
    obtain ⟨ib, hib, rfl⟩ := ho
    rw [Finset.mem_toList, Finset.mem_filter, Finset.mem_product] at hib
    exact ⟨ib.1, hib.1.1, ib.2, hib.2.1, hib.2.2, rfl⟩

lemma step_supp {k : ℕ} (x : Idx n k → ℂ) (s : ℂ × Pauli n × Finset (Fin n))
    (o : ℝ × ℂ × Pauli n × Finset (Fin n)) (ho : o ∈ alg2Step x s) (hs : support s.2.1 ⊆ s.2.2) : support o.2.2.1 ⊆ o.2.2.2 := by
  rcases mem_step x s o ho with rfl | ⟨i, _, b, _, _, h⟩
  · exact hs
  · rw [h]
    exact (support_adjTermPauli _ _).trans (Finset.union_subset_union hs le_rfl)

lemma rounds_supp {k : ℕ} (x : Idx n k → ℂ) (r : ℕ) (s : ℂ × Pauli n × Finset (Fin n))
    (hs : support s.2.1 ⊆ s.2.2) : ∀ o ∈ alg2Rounds x r s, support o.2.2.1 ⊆ o.2.2.2 := by
  induction r with
  | zero => intro o ho; simp [alg2Rounds] at ho; rw [ho]; exact hs
  | succ r ih =>
    intro o ho
    simp only [alg2Rounds] at ho
    rw [mem_bind] at ho
    obtain ⟨pa, hpa, qb, hqb, rfl⟩ := ho
    exact step_supp x pa.2 qb hqb (ih pa hpa)

lemma applySuper_list_sum {γ : Type*} (g : Super (Qubits n) (Qubits n)) (l : List γ)
    (F : γ → Op (Qubits n)) :
    applySuper g (l.map F).sum = (l.map (fun a => applySuper g (F a))).sum := by
  induction l with
  | nil => ext i j; simp [applySuper]
  | cons a l ih => simp [applySuper_add_right, ih]

lemma applySuper_eq_mulVec (g : Super (Qubits n) (Qubits n)) (X : Op (Qubits n)) (i j : Qubits n) :
    applySuper g X i j = Matrix.mulVec g (fun p => X p.1 p.2) (i, j) := by
  simp [applySuper, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

lemma applySuper_mul (g h : Super (Qubits n) (Qubits n)) (X : Op (Qubits n)) :
    applySuper (g * h) X = applySuper g (applySuper h X) := by
  ext i j
  rw [applySuper_eq_mulVec, applySuper_eq_mulVec, ← Matrix.mulVec_mulVec]
  congr 1
  funext p
  rw [applySuper_eq_mulVec]

lemma MExp_rounds {k : ℕ} (x : Idx n k → ℂ) (r : ℕ) (s : ℂ × Pauli n × Finset (Fin n))
    (hs : support s.2.1 ⊆ s.2.2) :
    MExp (alg2Rounds x r s) =
      applySuper (lindbladAdj (ext x) ^ r) (s.1 • pauliMatrix s.2.1) := by
  induction r with
  | zero =>
    simp only [alg2Rounds, MExp, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, Complex.ofReal_one, one_mul, pow_zero]
    ext i j
    simp only [applySuper, Matrix.one_apply, Prod.mk.injEq]
    simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
  | succ r ih =>
    simp only [alg2Rounds]
    rw [MExp_bind, pow_succ', applySuper_mul, ← ih]
    conv_rhs => rw [MExp]
    rw [applySuper_list_sum]
    congr 1
    apply List.map_congr_left
    intro pa hpa
    rw [MExp_step x pa.2 (rounds_supp x r s hs pa hpa), smul_smul, applySuper_smul_right]


lemma trace_adj_term (b : Pauli n × Pauli n) (Y X : Op (Qubits n)) :
    (applySuper (termAdj b) Y * X).trace = (Y * applySuper (termSuper b) X).trace := by
  rw [termAdj, termSuper, applySuper_sub, applySuper_sub, applySuper_smul, applySuper_smul,
    applySuper_add, applySuper_add]
  simp only [applySuper_leftRight, Matrix.mul_one, Matrix.one_mul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_add]
  have e1 : (pauliMatrix b.2 * Y * pauliMatrix b.1 * X).trace =
      (Y * (pauliMatrix b.1 * X * pauliMatrix b.2)).trace := by
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm (pauliMatrix b.2)]
    simp only [Matrix.mul_assoc]
  have e2 : (pauliMatrix b.2 * pauliMatrix b.1 * Y * X).trace =
      (Y * (X * (pauliMatrix b.2 * pauliMatrix b.1))).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have e3 : (Y * (pauliMatrix b.2 * pauliMatrix b.1) * X).trace =
      (Y * (pauliMatrix b.2 * pauliMatrix b.1 * X)).trace := by
    rw [Matrix.mul_assoc]
  rw [e1, e2, e3]
  ring

lemma ntr_adj (x : Pauli n × Pauli n → ℂ) (Y X : Op (Qubits n)) :
    ntr (applySuper (lindbladAdj x) Y * X) = ntr (Y * applySuper (lindbladSuper x) X) := by
  unfold ntr
  congr 1
  rw [lindbladAdj_eq, lindbladSuper_eq, applySuper_sum, applySuper_sum, Finset.sum_mul,
    Matrix.mul_sum, Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [applySuper_smul, applySuper_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.trace_smul, trace_adj_term]

lemma ntr_adj_pow (x : Pauli n × Pauli n → ℂ) (r : ℕ) (Y X : Op (Qubits n)) :
    ntr (applySuper (lindbladAdj x ^ r) Y * X) = ntr (Y * applySuper (lindbladSuper x ^ r) X) := by
  induction r generalizing Y X with
  | zero =>
    have h1 : ∀ Z : Op (Qubits n), applySuper (1 : Super (Qubits n) (Qubits n)) Z = Z := by
      intro Z; ext i j
      simp only [applySuper, Matrix.one_apply, Prod.mk.injEq]
      simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
    rw [pow_zero, pow_zero, h1, h1]
  | succ r ih =>
    rw [pow_succ, applySuper_mul, ih, ntr_adj, pow_succ', applySuper_mul]

lemma expect_ntr (μ : FinDist (ℂ × Pauli n × Finset (Fin n))) (X : Op (Qubits n)) :
    FinDist.expect μ (fun o => o.1 * ntr (pauliMatrix o.2.1 * X)) = ntr (MExp μ * X) := by
  induction μ with
  | nil => simp [FinDist.expect, MExp, ntr]
  | cons o μ ih =>
    simp only [FinDist.expect, MExp, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Matrix.add_mul, ntr_add, Matrix.smul_mul, ntr_smul]
    ring

lemma card_paulisOn (S : Finset (Fin n)) : (paulisOn S).card = 4 ^ S.card := by
  rw [paulisOn_eq_piFinset, Fintype.card_piFinset]
  have : ∀ i, ((if i ∈ S then (Finset.univ : Finset (Fin 4)) else {0}) : Finset (Fin 4)).card =
      if i ∈ S then 4 else 1 := by
    intro i; split_ifs <;> simp
  simp_rw [this]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

theorem lemma_4_9_expect {k : ℕ} (x : Idx n k → ℂ) (ℓ : ℕ) (P : Pauli n × Pauli n) :
    FinDist.expect (alg2Law x P ℓ) id = Eell ℓ (ext x) P := by
  unfold alg2Law Eell
  rw [expect_bind]
  have key : ∀ (μ : FinDist (Pauli n)) (h : Pauli n → ℂ),
      (μ.map (fun pa => (pa.1 : ℂ) * h pa.2)).sum = FinDist.expect μ h := fun _ _ => rfl
  rw [key (FinDist.uniform (paulisOn (pairSupport P))) (fun R => FinDist.expect
    (List.map (fun o => (o.1, o.2.1 * ntr (pauliMatrix o.2.2.1 * pauliMatrix R)))
      (alg2Rounds x ℓ (pauliPhase P.2 R * pauliPhase (pauliProd P.2 R) P.1,
        pauliProd (pauliProd P.2 R) P.1, pairSupport P))) id)]
  rw [expect_uniform, pauliAvg, card_paulisOn]
  push_cast
  congr 1
  refine Finset.sum_congr rfl (fun R hR => ?_)
  rw [expect_map _ (fun o : ℂ × Pauli n × Finset (Fin n) =>
    o.1 * ntr (pauliMatrix o.2.1 * pauliMatrix R)) id]
  have hcomp : (id ∘ fun o : ℂ × Pauli n × Finset (Fin n) =>
      o.1 * ntr (pauliMatrix o.2.1 * pauliMatrix R)) =
      fun o => o.1 * ntr (pauliMatrix o.2.1 * pauliMatrix R) := rfl
  rw [hcomp, expect_ntr, MExp_rounds]
  · rw [ntr_adj_pow]
    congr 2
    simp only [chi, Matrix.conjTranspose_mul, pauliMatrix_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc, pauliMatrix_mul P.2, Matrix.smul_mul, pauliMatrix_mul, smul_smul]
  · simp only [paulisOn, Finset.mem_filter, Finset.mem_univ, true_and] at hR
    exact pauliProd_mem _ _ _ (pauliProd_mem _ _ _ Finset.subset_union_right hR)
      Finset.subset_union_left


lemma alg2Weight_le {k : ℕ} (x : Idx n k → ℂ) (i : Fin n) : alg2Weight x i ≤ b1Norm (ext x) := by
  refine le_trans (le_of_eq ?_) (ss_le_b1 x i)
  unfold alg2Weight ss
  rw [Finset.sum_filter]

lemma norm_pauliPhase (P Q : Pauli n) : ‖pauliPhase P Q‖ = 1 := by
  rw [pauliPhase, norm_prod]; simp [norm_letterPhase]

lemma norm_adjTermCoeff (b : Pauli n × Pauli n) (Q : Pauli n) : ‖adjTermCoeff b Q‖ ≤ 2 := by
  unfold adjTermCoeff
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_pauliPhase, norm_pauliPhase]
  have : ‖pauliPhase b.2 b.1 * pauliPhase (pauliProd b.2 b.1) Q +
      pauliPhase Q b.2 * pauliPhase (pauliProd Q b.2) b.1‖ ≤ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    simp only [norm_pauliPhase]; norm_num
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h12]
  linarith

lemma step_bound {k : ℕ} (x : Idx n k → ℂ) (g : ℝ) (hx : b1Norm (ext x) ≤ g)
    (s : ℂ × Pauli n × Finset (Fin n)) (o : ℝ × ℂ × Pauli n × Finset (Fin n))
    (ho : o ∈ alg2Step x s) (hk : ∀ b : Idx n k, (pairSupport b.1).card ≤ k) :
    ‖o.2.1‖ ≤ ‖s.1‖ * (2 * (s.2.2.card * g)) ∧ o.2.2.2.card ≤ s.2.2.card + k := by
  have hg : 0 ≤ g := le_trans (by rw [b1Norm_ext_eq]; exact NNReal.coe_nonneg _) hx
  rcases mem_step x s o ho with rfl | ⟨i, hiA, b, hib, hxb, h⟩
  · simp only [norm_zero]
    refine ⟨by positivity, by omega⟩
  · rw [h]
    simp only
    set W : ℝ := ∑ j ∈ s.2.2, alg2Weight x j
    have hW0 : 0 ≤ W := Finset.sum_nonneg (fun j _ => alg2Weight_nonneg x j)
    have hWle : W ≤ s.2.2.card * g := by
      calc W ≤ ∑ j ∈ s.2.2, g := Finset.sum_le_sum (fun j _ => (alg2Weight_le x j).trans hx)
        _ = s.2.2.card * g := by simp
    have hcard : (1 : ℝ) ≤ (s.2.2 ∩ pairSupport b.1).card := by
      have : 0 < (s.2.2 ∩ pairSupport b.1).card :=
        Finset.card_pos.2 ⟨i, Finset.mem_inter.2 ⟨hiA, hib⟩⟩
      exact_mod_cast this
    constructor
    · rw [norm_mul, norm_mul, norm_mul, norm_div, norm_div]
      have hxn : ‖x b‖ ≠ 0 := norm_ne_zero_iff.2 hxb
      rw [Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hW0,
        Real.norm_of_nonneg (norm_nonneg _), div_self hxn, mul_one]
      have hc : ‖((s.2.2 ∩ pairSupport b.1).card : ℂ)‖ = (s.2.2 ∩ pairSupport b.1).card := by
        rw [Complex.norm_natCast]
      rw [hc]
      have h1 : W / (s.2.2 ∩ pairSupport b.1).card ≤ s.2.2.card * g :=
        (div_le_self hW0 hcard).trans hWle
      have h2 := norm_adjTermCoeff b.1 s.2.1
      have h3 : 0 ≤ W / (s.2.2 ∩ pairSupport b.1).card := div_nonneg hW0 (by positivity)
      calc ‖s.1‖ * (W / (s.2.2 ∩ pairSupport b.1).card) * ‖adjTermCoeff b.1 s.2.1‖
          ≤ ‖s.1‖ * (s.2.2.card * g) * 2 := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) h2 (norm_nonneg _)
            positivity
        _ = ‖s.1‖ * (2 * (s.2.2.card * g)) := by ring
    · exact (Finset.card_union_le _ _).trans (by have := hk b; omega)

lemma rounds_bound {k : ℕ} (x : Idx n k → ℂ) (g : ℝ) (hx : b1Norm (ext x) ≤ g)
    (hk : ∀ b : Idx n k, (pairSupport b.1).card ≤ k) (r : ℕ)
    (s : ℂ × Pauli n × Finset (Fin n)) (hs1 : ‖s.1‖ ≤ 1) (hs2 : s.2.2.card ≤ k) :
    ∀ o ∈ alg2Rounds x r s, ‖o.2.1‖ ≤ r.factorial * (2 * k * g) ^ r ∧
      o.2.2.2.card ≤ k * (r + 1) := by
  have hg : 0 ≤ g := le_trans (by rw [b1Norm_ext_eq]; exact NNReal.coe_nonneg _) hx
  induction r with
  | zero =>
    intro o ho
    simp [alg2Rounds] at ho
    rw [ho]
    simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one, zero_add]
    exact ⟨hs1, hs2⟩
  | succ r ih =>
    intro o ho
    simp only [alg2Rounds] at ho
    rw [mem_bind] at ho
    obtain ⟨pa, hpa, qb, hqb, rfl⟩ := ho
    obtain ⟨h1, h2⟩ := ih pa hpa
    obtain ⟨h3, h4⟩ := step_bound x g hx pa.2 qb hqb hk
    refine ⟨?_, ?_⟩
    · simp only
      refine h3.trans ?_
      have hc : (pa.2.2.2.card : ℝ) ≤ k * (r + 1) := by exact_mod_cast h2
      calc ‖pa.2.1‖ * (2 * (pa.2.2.2.card * g))
          ≤ (r.factorial * (2 * k * g) ^ r) * (2 * ((k * (r + 1)) * g)) := by
            apply mul_le_mul h1 _ (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hg) (by norm_num)
        _ = ((r + 1).factorial : ℝ) * (2 * k * g) ^ (r + 1) := by
            rw [Nat.factorial_succ]; push_cast; ring
    · simp only; nlinarith [h4, h2]

lemma norm_ntr_pauli (Q R : Pauli n) : ‖ntr (pauliMatrix Q * pauliMatrix R)‖ ≤ 1 := by
  rw [pauliMatrix_eq_tens, pauliMatrix_eq_tens, tens_mul, ntr_tens, norm_prod]
  apply Finset.prod_le_one (fun i _ => norm_nonneg _)
  intro i _
  rw [trace_onePauli_mul]
  split_ifs <;> norm_num

lemma alg2_bound_all {k : ℕ} (g : ℝ) (x : Idx n k → ℂ)
    (hx : b1Norm (ext x) ≤ g) (ℓ : ℕ) (P : Pauli n × Pauli n) (hP : (pairSupport P).card ≤ k) :
    ∀ o ∈ alg2Law x P ℓ, ‖o.2‖ ≤ (ℓ.factorial : ℝ) * (2 * k * g) ^ ℓ := by
  intro o ho
  unfold alg2Law at ho
  rw [mem_bind] at ho
  obtain ⟨pa, _, qb, hqb, rfl⟩ := ho
  rw [List.mem_map] at hqb
  obtain ⟨oo, hoo, rfl⟩ := hqb
  simp only
  have hb := rounds_bound x g hx (fun b => b.2.2) ℓ _ (by
    simp only; rw [norm_mul, norm_pauliPhase, norm_pauliPhase]; norm_num) hP oo hoo
  rw [norm_mul]
  calc ‖oo.2.1‖ * ‖ntr (pauliMatrix oo.2.2.1 * pauliMatrix pa.2)‖ ≤ ‖oo.2.1‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_ntr_pauli _ _) (norm_nonneg _)
    _ ≤ _ := by rw [mul_one]; exact hb.1



theorem lemma_4_9_aux {k : ℕ} (hk : 0 < k) (g : ℝ) (hg : 0 < g) (x : Idx n k → ℂ)
    (hx : b1Norm (ext x) ≤ g) (ℓ : ℕ) (P : Pauli n × Pauli n) (hP : (pairSupport P).card ≤ k) :
    FinDist.expect (alg2Law x P ℓ) id = Eell ℓ (ext x) P ∧
      ∀ o ∈ alg2Law x P ℓ, 0 < o.1 → ‖o.2‖ ≤ (ℓ.factorial : ℝ) * (2 * k * g) ^ ℓ := by
  refine ⟨lemma_4_9_expect x ℓ P, fun o ho _ => alg2_bound_all g x hx ℓ P hP o ho⟩


end LindbladStructLearn.AAux


namespace LindbladStructLearn.AAux
open LindbladTolerant.Testing LindbladStructLearn LindbladStructLearn.FourierAux

variable {n : ℕ}

lemma pauliMatrix_mul_self (Q : Pauli n) : pauliMatrix Q * pauliMatrix Q = 1 := by
  rw [pauliMatrix_mul]
  have h1 : pauliPhase Q Q = 1 := by simp [pauliPhase, letterPhase_self]
  have h2 : pauliProd Q Q = 0 := by funext i; simp [pauliProd, letterMul_self]
  rw [h1, h2, pauliMatrix_zero, one_smul]

lemma norm_clm_pauli (Q : Pauli n) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Qubits n) (pauliMatrix Q)‖ ≤ 1 := by
  set U := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Qubits n) (pauliMatrix Q)
  have hU : star U * U = 1 := by
    simp only [U, ← map_star, ← map_mul]
    rw [show star (pauliMatrix Q) = (pauliMatrix Q)ᴴ from rfl, pauliMatrix_conjTranspose,
      pauliMatrix_mul_self, map_one]
  have h := CStarRing.norm_star_mul_self (x := U)
  rw [hU] at h
  have h1 : ‖(1 : EuclideanSpace ℂ (Qubits n) →L[ℂ] EuclideanSpace ℂ (Qubits n))‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  nlinarith [norm_nonneg U]

lemma step_mass {k : ℕ} (x : Idx n k → ℂ) (s : ℂ × Pauli n × Finset (Fin n)) :
    ((alg2Step x s).map (fun o => o.1)).sum = 1 ∧ ∀ o ∈ alg2Step x s, 0 ≤ o.1 := by
  classical
  unfold alg2Step
  simp only
  split_ifs with hW
  · simp
  · push Not at hW
    obtain ⟨hW0, _⟩ := hW
    set A := s.2.2
    set W : ℝ := ∑ j ∈ A, alg2Weight x j with hWdef
    have hWpos : 0 < W := lt_of_le_of_ne (Finset.sum_nonneg
      (fun j _ => alg2Weight_nonneg x j)) (Ne.symm hW0)
    constructor
    · rw [List.map_map, Finset.sum_map_toList]
      simp only [Function.comp_def]
      have : ∀ ib ∈ (A ×ˢ (Finset.univ : Finset (Idx n k))).filter
          (fun ib => ib.1 ∈ pairSupport ib.2.1 ∧ x ib.2 ≠ 0),
          alg2Weight x ib.1 / W * (‖x ib.2‖ / alg2Weight x ib.1) = ‖x ib.2‖ / W := by
        intro ib hib
        simp only [Finset.mem_filter, Finset.mem_product] at hib
        have hwi : alg2Weight x ib.1 ≠ 0 := ne_of_gt (lt_of_lt_of_le (norm_pos_iff.2 hib.2.2)
          (norm_le_alg2Weight x ib.1 ib.2 hib.2.1))
        field_simp
      rw [Finset.sum_congr rfl this, ← Finset.sum_div, div_eq_one_iff_eq hW0]
      rw [Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      unfold alg2Weight
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      by_cases h1 : i ∈ pairSupport b.1
      · by_cases h2 : x b = 0
        · simp [h1, h2]
        · simp [h1, h2]
      · simp [h1]
    · intro o ho
      rw [List.mem_map] at ho
      obtain ⟨ib, _, rfl⟩ := ho
      exact mul_nonneg (div_nonneg (alg2Weight_nonneg _ _) hWpos.le)
        (div_nonneg (norm_nonneg _) (alg2Weight_nonneg _ _))

lemma rounds_mass {k : ℕ} (x : Idx n k → ℂ) (r : ℕ) (s : ℂ × Pauli n × Finset (Fin n)) :
    ((alg2Rounds x r s).map (fun o => o.1)).sum = 1 ∧ ∀ o ∈ alg2Rounds x r s, 0 ≤ o.1 := by
  induction r with
  | zero => simp [alg2Rounds]
  | succ r ih =>
    simp only [alg2Rounds]
    constructor
    · have key : ∀ (μ : FinDist (ℂ × Pauli n × Finset (Fin n))),
          ((FinDist.bind μ (alg2Step x)).map (fun o => o.1)).sum = (μ.map (fun o => o.1)).sum := by
        intro μ
        induction μ with
        | nil => simp [FinDist.bind]
        | cons pa μ ihμ =>
          have := (step_mass x pa.2).1
          simp only [FinDist.bind, List.flatMap_cons, List.map_append, List.sum_append,
            List.map_cons, List.sum_cons] at ihμ ⊢
          rw [ihμ, List.map_map]
          congr 1
          simp only [Function.comp_def]
          have h2 : ∀ (l : FinDist (ℂ × Pauli n × Finset (Fin n))) (c : ℝ),
              (l.map (fun o => c * o.1)).sum = c * (l.map (fun o => o.1)).sum := by
            intro l c
            induction l with
            | nil => simp
            | cons a l ihl => simp [ihl, mul_add]
          rw [h2, this, mul_one]
      rw [key, ih.1]
    · intro o ho
      rw [mem_bind] at ho
      obtain ⟨pa, hpa, qb, hqb, rfl⟩ := ho
      exact mul_nonneg (ih.2 pa hpa) ((step_mass x pa.2).2 qb hqb)

lemma norm_MExp_le (μ : FinDist (ℂ × Pauli n × Finset (Fin n))) (B : ℝ)
    (hB : ∀ o ∈ μ, ‖o.2.1‖ ≤ B) (hpos : ∀ o ∈ μ, 0 ≤ o.1) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Qubits n) (MExp μ)‖ ≤
      (μ.map (fun o => o.1)).sum * B := by
  induction μ with
  | nil => simp [MExp]
  | cons o μ ih =>
    simp only [MExp, List.map_cons, List.sum_cons, map_add] at ih ⊢
    refine (norm_add_le _ _).trans ?_
    rw [add_mul]
    refine add_le_add ?_ (ih (fun o' h => hB o' (List.mem_cons_of_mem _ h))
      (fun o' h => hpos o' (List.mem_cons_of_mem _ h)))
    rw [map_smul, norm_smul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (hpos o List.mem_cons_self)]
    have := norm_clm_pauli (n := n) o.2.2.1
    have hb := hB o List.mem_cons_self
    calc o.1 * ‖o.2.1‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Qubits n) (pauliMatrix o.2.2.1)‖
        ≤ o.1 * B * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hb (hpos o List.mem_cons_self)) this
            (norm_nonneg _)
          exact mul_nonneg (hpos o List.mem_cons_self) ((norm_nonneg _).trans hb)
      _ = o.1 * B := by ring


lemma ext_toIdx_of_local {k : ℕ} (lam : Pauli n × Pauli n → ℂ) (hloc : IsKLocal k lam)
    (P : Pauli n × Pauli n) (hP : P.1 ≠ 0) : ext (toIdx (k := k) lam) P = lam P := by
  unfold ext
  split_ifs with h
  · rfl
  · by_contra hne
    exact h ⟨hP, hloc P hP (Ne.symm hne)⟩

lemma lindbladAdj_toIdx {k : ℕ} (lam : Pauli n × Pauli n → ℂ) (hloc : IsKLocal k lam) :
    lindbladAdj (ext (toIdx (k := k) lam)) = lindbladAdj lam := by
  rw [lindbladAdj_eq, lindbladAdj_eq]
  refine Finset.sum_congr rfl (fun P hP => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP
  rw [ext_toIdx_of_local lam hloc P hP]

lemma b1Norm_toIdx {k : ℕ} (lam : Pauli n × Pauli n → ℂ) (hloc : IsKLocal k lam) :
    b1Norm (ext (toIdx (k := k) lam)) = b1Norm lam := by
  unfold b1Norm
  congr 2
  funext i
  refine Finset.sum_congr rfl (fun P hP => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP
  rw [ext_toIdx_of_local lam hloc P hP.1]

theorem corollary_4_6_aux (k : ℕ) (hk : 0 < k) (g : ℝ) (hg : 0 < g)
    (lam : Pauli n × Pauli n → ℂ) (hloc : IsKLocal k lam) (hB1 : b1Norm lam ≤ g)
    (P : Pauli n) (hP : weight P ≤ k) (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Qubits n)
        (applySuper (lindbladAdj lam ^ ℓ) (pauliMatrix P))‖ ≤
      (ℓ.factorial : ℝ) * (2 * Real.exp 1 * k * g) ^ ℓ := by
  set x : Idx n k → ℂ := toIdx lam
  have hx : b1Norm (ext x) ≤ g := by rw [b1Norm_toIdx lam hloc]; exact hB1
  rw [← lindbladAdj_toIdx (k := k) lam hloc]
  have hM := MExp_rounds x ℓ ((1 : ℂ), P, support P) le_rfl
  simp only [one_smul] at hM
  rw [← hM]
  have hbd := rounds_bound x g hx (fun b => b.2.2) ℓ ((1 : ℂ), P, support P) (by simp) hP
  have hmass := rounds_mass x ℓ ((1 : ℂ), P, support P)
  refine (norm_MExp_le _ ((ℓ.factorial : ℝ) * (2 * k * g) ^ ℓ)
    (fun o ho => (hbd o ho).1) hmass.2).trans ?_
  rw [hmass.1, one_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  have he : (1 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have : (0 : ℝ) ≤ k * g := by positivity
  nlinarith

end LindbladStructLearn.AAux

open LindbladTolerant.Testing LindbladStructLearn

theorem solution {n : ℕ} (k : ℕ) (hk : 0 < k) (g : ℝ) (hg : 0 < g)
    (lam : Pauli n × Pauli n → ℂ) (hloc : IsKLocal k lam) (hB1 : b1Norm lam ≤ g)
    (P : Pauli n) (hP : weight P ≤ k) (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Qubits n)
        (applySuper (lindbladAdj lam ^ ℓ) (pauliMatrix P))‖ ≤
      (ℓ.factorial : ℝ) * (2 * Real.exp 1 * k * g) ^ ℓ :=
  LindbladStructLearn.AAux.corollary_4_6_aux k hk g hg lam hloc hB1 P hP ℓ hℓ
