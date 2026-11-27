-- Prove2me | solution 1 for LindbladStructLearn.proposition_2_9
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T22:57:19.890356+00:00
-- url     : https://prove2.me/submissions/b73195c8-6bd5-4c57-95ee-8573b926cb88

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_LindbladStructLearn_alg1Sample
import Definitions.Def_LindbladStructLearn_bornAmp
import Definitions.Def_LindbladStructLearn_locFourier
import Definitions.Def_LindbladStructLearn_Amat
import Definitions.Def_LindbladStructLearn_Vmat

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

open LindbladTolerant.Testing LindbladStructLearn

theorem solution {n : ℕ} (Φ : Super (Qubits n) (Qubits n)) (P : Pauli n × Pauli n) :
    ∑ A : Pauli n, ∑ v : Qubits n, ∑ B : Pauli n, ∑ w : Qubits n,
      ((1 / 4 ^ n : ℂ) * (1 / 2 ^ n) * (1 / 4 ^ n)) * bornAmp Φ A v B w * alg1Sample P A v B w =
      locFourier Φ P :=
  LindbladStructLearn.AAux.proposition_2_9_aux Φ P
