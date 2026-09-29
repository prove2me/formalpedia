-- Prove2me | solution 1 for MarkovEntanglement.agentwise_marginal_independence_implies_separable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-09T16:04:41.522516+00:00
-- url     : https://prove2.me/submissions/ef6fbba9-5e56-434e-82d5-cde44817f0dd

import Definitions.Def_markov_entanglement_multi

open scoped BigOperators

namespace MarkovEntanglement

variable {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-! ### Part 5. A resolution of the identity on one agent's matrix space

Fix a base state `o`.  Every elementary matrix `E a b` decomposes as

  `E a b = D a b + (1/m - 1) • C o + G a`,

where `D a b` sends `a ↦ b` and everything else to `o`, `C o = D o o` sends everything to `o`
(both are *transition matrices*), and `G a p q = [q = o] * ([p = a] - 1/m)` is a correction whose
family sums to zero.  Writing this as a single indexed family over `(M × M) ⊕ M` gives a
resolution of the identity whose `inl` part is stochastic and whose `inr` coefficients are
independent of the column index and sum to zero over the row index — exactly the two properties
the tensor argument needs. -/

section Factor

variable {M : Type*} [Fintype M] [DecidableEq M]

/-- The deterministic transition sending `st.1` to `st.2` and every other state to `o`. -/
def detMat (o : M) (st : M × M) : Matrix M M ℝ :=
  fun p q => if p = st.1 then (if q = st.2 then (1 : ℝ) else 0) else (if q = o then (1 : ℝ) else 0)

/-- The correction direction attached to row `s`. -/
noncomputable def cplMat (o : M) (s : M) : Matrix M M ℝ :=
  fun p q => (if q = o then (1 : ℝ) else 0) * ((if p = s then (1 : ℝ) else 0)
    - 1 / (Fintype.card M : ℝ))

/-- The resolving family. -/
noncomputable def resVec (o : M) : (M × M) ⊕ M → Matrix M M ℝ :=
  Sum.elim (fun st => detMat o st) (fun s => cplMat o s)

/-- The dual coefficients of the resolving family. -/
noncomputable def resDual (o : M) : ((M × M) ⊕ M) → M → M → ℝ :=
  Sum.elim
    (fun st a b => (if (a, b) = st then (1 : ℝ) else 0)
      + (if (o, o) = st then 1 / (Fintype.card M : ℝ) - 1 else 0))
    (fun s a _ => (if a = s then (1 : ℝ) else 0) - 1 / (Fintype.card M : ℝ))

/-- A stochastic stand-in for the whole family: it agrees with `resVec` on the `inl` part, and
on the `inr` part it is an arbitrary transition matrix (those coefficients vanish anyway). -/
def goodVec (o : M) : ((M × M) ⊕ M) → Matrix M M ℝ :=
  Sum.elim (fun st => detMat o st) (fun _ => detMat o (o, o))

lemma detMat_isTransition (o : M) (st : M × M) : IsTransitionMatrix (detMat o st) := by
  refine ⟨fun p q => ?_, fun p => ?_⟩
  · simp only [detMat]; split <;> split <;> norm_num
  · simp only [detMat]; split <;> simp

lemma goodVec_isTransition (o : M) (x : (M × M) ⊕ M) : IsTransitionMatrix (goodVec o x) := by
  cases x with
  | inl st => exact detMat_isTransition o st
  | inr s => exact detMat_isTransition o (o, o)

lemma resVec_inl (o : M) (st : M × M) : resVec o (Sum.inl st) = goodVec o (Sum.inl st) := rfl

lemma sum_cplMat (o : M) [Nonempty M] (p q : M) : ∑ s : M, cplMat o s p q = 0 := by
  have hcard : (Fintype.card M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h1 : ∑ _s : M, ((if p = _s then (1 : ℝ) else 0) - 1 / (Fintype.card M : ℝ)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq Finset.univ p (fun _ => (1 : ℝ))]
    simp only [Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_one_div, div_self hcard, sub_self]
  calc ∑ s : M, cplMat o s p q
      = ∑ s : M, (if q = o then (1 : ℝ) else 0)
          * ((if p = s then (1 : ℝ) else 0) - 1 / (Fintype.card M : ℝ)) := rfl
    _ = (if q = o then (1 : ℝ) else 0)
          * ∑ s : M, ((if p = s then (1 : ℝ) else 0) - 1 / (Fintype.card M : ℝ)) := by
        rw [Finset.mul_sum]
    _ = 0 := by rw [h1, mul_zero]

/-- **Resolution of the identity.** -/
lemma resolution (o : M) [Nonempty M] (a b p q : M) :
    ∑ x : (M × M) ⊕ M, resDual o x a b * resVec o x p q
      = (if p = a then (1 : ℝ) else 0) * (if q = b then (1 : ℝ) else 0) := by
  have hcard : (Fintype.card M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Fintype.sum_sum_type]
  have h1 : ∑ st : M × M, resDual o (Sum.inl st) a b * resVec o (Sum.inl st) p q
      = detMat o (a, b) p q + (1 / (Fintype.card M : ℝ) - 1) * detMat o (o, o) p q := by
    simp only [resDual, resVec, Sum.elim_inl, add_mul]
    rw [Finset.sum_add_distrib]
    congr 1
    · simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq Finset.univ (a, b) (fun st => detMat o st p q)]
      simp
    · simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq Finset.univ (o, o)
        (fun st => (1 / (Fintype.card M : ℝ) - 1) * detMat o st p q)]
      simp
  have h2 : ∑ s : M, resDual o (Sum.inr s) a b * resVec o (Sum.inr s) p q
      = cplMat o a p q := by
    simp only [resDual, resVec, Sum.elim_inr, sub_mul]
    rw [Finset.sum_sub_distrib]
    have e1 : ∑ s : M, (if a = s then (1 : ℝ) else 0) * cplMat o s p q = cplMat o a p q := by
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq Finset.univ a (fun s => cplMat o s p q)]
      simp
    have e2 : ∑ s : M, 1 / (Fintype.card M : ℝ) * cplMat o s p q = 0 := by
      rw [← Finset.mul_sum, sum_cplMat o p q, mul_zero]
    rw [e1, e2, sub_zero]
  rw [h1, h2]
  simp only [detMat, cplMat]
  by_cases hpa : p = a <;> by_cases hqo : q = o <;> simp [hpa, hqo]
  all_goals ring

lemma resDual_inr_apply (o : M) (s a b : M) :
    resDual o (Sum.inr s) a b = (if a = s then (1 : ℝ) else 0) - 1 / (Fintype.card M : ℝ) := rfl

lemma sum_resDual_inr (o : M) [Nonempty M] (s b : M) :
    ∑ a : M, resDual o (Sum.inr s) a b = 0 := by
  have hcard : (Fintype.card M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [resDual_inr_apply]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ s (fun _ => (1 : ℝ))]
  simp only [Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_one_div, div_self hcard, sub_self]

end Factor

/-! ### Part 6. The tensor expansion of an arbitrary joint matrix -/

/-- An index for the tensor-product resolution: one factor index per agent. -/
abbrev SepIdx (S : Fin N → Type*) : Type _ := ∀ i, (S i × S i) ⊕ S i

lemma prod_ite_eq_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    [∀ i, DecidableEq (β i)] (p a : ∀ i, β i) :
    ∏ i, (if p i = a i then (1 : ℝ) else 0) = if p = a then 1 else 0 := by
  by_cases h : p = a
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma sum_prod_eq_one (Ml : ∀ i, Matrix (S i) (S i) ℝ) (hMl : ∀ i, IsTransitionMatrix (Ml i))
    (p : Joint S) : ∑ q : Joint S, ∏ i, Ml i (p i) (q i) = 1 := by
  classical
  rw [show (Finset.univ : Finset (Joint S))
      = Fintype.piFinset (fun i => (Finset.univ : Finset (S i))) from Fintype.piFinset_univ.symm,
    ← Finset.prod_univ_sum]
  exact Finset.prod_eq_one fun i _ => (hMl i).2 (p i)

/-- The coefficient of the tensor-product resolution at index `x`. -/
noncomputable def sepCoef (P : Matrix (Joint S) (Joint S) ℝ) (o : Joint S) (x : SepIdx S) : ℝ :=
  ∑ a : Joint S, ∑ b : Joint S, (∏ i, resDual (o i) (x i) (a i) (b i)) * P a b

lemma sep_expansion (P : Matrix (Joint S) (Joint S) ℝ) (o : Joint S) (p q : Joint S) :
    P p q = ∑ x : SepIdx S, sepCoef P o x * ∏ i, resVec (o i) (x i) (p i) (q i) := by
  classical
  haveI : ∀ i, Nonempty (S i) := fun i => ⟨o i⟩
  have key : ∀ a b : Joint S,
      ∑ x : SepIdx S,
          (∏ i, resDual (o i) (x i) (a i) (b i)) * ∏ i, resVec (o i) (x i) (p i) (q i)
        = (if p = a then (1 : ℝ) else 0) * (if q = b then (1 : ℝ) else 0) := by
    intro a b
    have h1 : ∀ x : SepIdx S,
        (∏ i, resDual (o i) (x i) (a i) (b i)) * ∏ i, resVec (o i) (x i) (p i) (q i)
          = ∏ i, (resDual (o i) (x i) (a i) (b i) * resVec (o i) (x i) (p i) (q i)) :=
      fun x => (Finset.prod_mul_distrib).symm
    have hps := Finset.prod_univ_sum
      (fun i => (Finset.univ : Finset ((S i × S i) ⊕ S i)))
      (fun i (y : (S i × S i) ⊕ S i) =>
        resDual (o i) y (a i) (b i) * resVec (o i) y (p i) (q i))
    rw [Finset.sum_congr rfl fun x _ => h1 x,
      show (Finset.univ : Finset (SepIdx S))
        = Fintype.piFinset (fun i => (Finset.univ : Finset ((S i × S i) ⊕ S i))) from
        Fintype.piFinset_univ.symm,
      ← hps,
      Finset.prod_congr rfl fun i _ => resolution (o i) (a i) (b i) (p i) (q i),
      Finset.prod_mul_distrib, prod_ite_eq_pi, prod_ite_eq_pi]
  have inner : ∀ a : Joint S,
      ∑ b : Joint S, P a b * ((if p = a then (1 : ℝ) else 0) * (if q = b then (1 : ℝ) else 0))
        = (if p = a then (1 : ℝ) else 0) * P a q := by
    intro a
    have hb : ∀ b : Joint S,
        P a b * ((if p = a then (1 : ℝ) else 0) * (if q = b then (1 : ℝ) else 0))
          = if q = b then (if p = a then (1 : ℝ) else 0) * P a b else 0 := by
      intro b; by_cases h2 : q = b <;> simp [h2] <;> ring
    rw [Finset.sum_congr rfl fun b _ => hb b,
      Finset.sum_ite_eq Finset.univ q (fun b => (if p = a then (1 : ℝ) else 0) * P a b)]
    simp
  have first : P p q
      = ∑ a : Joint S, ∑ b : Joint S,
          P a b * ((if p = a then (1 : ℝ) else 0) * (if q = b then (1 : ℝ) else 0)) := by
    rw [Finset.sum_congr rfl fun a _ => inner a]
    have ha : ∀ a : Joint S, (if p = a then (1 : ℝ) else 0) * P a q
        = if p = a then P a q else 0 := by
      intro a; by_cases h1 : p = a <;> simp [h1]
    rw [Finset.sum_congr rfl fun a _ => ha a,
      Finset.sum_ite_eq Finset.univ p (fun a => P a q)]
    simp
  rw [first]
  have step : ∀ a b : Joint S,
      P a b * ((if p = a then (1 : ℝ) else 0) * (if q = b then (1 : ℝ) else 0))
        = ∑ x : SepIdx S, ((∏ i, resDual (o i) (x i) (a i) (b i)) * P a b)
            * ∏ i, resVec (o i) (x i) (p i) (q i) := by
    intro a b
    have hmv : ∑ x : SepIdx S, ((∏ i, resDual (o i) (x i) (a i) (b i)) * P a b)
          * ∏ i, resVec (o i) (x i) (p i) (q i)
        = P a b * ∑ x : SepIdx S,
            (∏ i, resDual (o i) (x i) (a i) (b i)) * ∏ i, resVec (o i) (x i) (p i) (q i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hmv, key a b]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => step a b]
  have rhs_eq : ∑ x : SepIdx S, sepCoef P o x * ∏ i, resVec (o i) (x i) (p i) (q i)
      = ∑ x : SepIdx S, ∑ a : Joint S, ∑ b : Joint S,
          ((∏ i, resDual (o i) (x i) (a i) (b i)) * P a b)
            * ∏ i, resVec (o i) (x i) (p i) (q i) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [sepCoef, Finset.sum_mul]
  rw [rhs_eq]
  calc ∑ a : Joint S, ∑ b : Joint S, ∑ x : SepIdx S,
          ((∏ i, resDual (o i) (x i) (a i) (b i)) * P a b)
            * ∏ i, resVec (o i) (x i) (p i) (q i)
      = ∑ a : Joint S, ∑ x : SepIdx S, ∑ b : Joint S,
          ((∏ i, resDual (o i) (x i) (a i) (b i)) * P a b)
            * ∏ i, resVec (o i) (x i) (p i) (q i) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ x : SepIdx S, ∑ a : Joint S, ∑ b : Joint S,
          ((∏ i, resDual (o i) (x i) (a i) (b i)) * P a b)
            * ∏ i, resVec (o i) (x i) (p i) (q i) := Finset.sum_comm

/-! ### Part 7. Coefficients at a `inr` index vanish -/

/-- Swapping agent `i`'s coordinate with a spare state is an involution of `Joint S × S i`. -/
def coordSwap (i : Fin N) : (Joint S × S i) ≃ (Joint S × S i) where
  toFun x := (Function.update x.1 i x.2, x.1 i)
  invFun x := (Function.update x.1 i x.2, x.1 i)
  left_inv := by
    rintro ⟨b, t⟩
    simp [Function.update_idem, Function.update_self, Function.update_eq_self]
  right_inv := by
    rintro ⟨b, t⟩
    simp [Function.update_idem, Function.update_self, Function.update_eq_self]

lemma sum_coordSwap (i : Fin N) (F : Joint S → S i → ℝ) :
    ∑ b : Joint S, ∑ t : S i, F (Function.update b i t) (b i)
      = ∑ c : Joint S, ∑ u : S i, F c u := by
  have h := Equiv.sum_comp (coordSwap (S := S) i) (fun x : Joint S × S i => F x.1 x.2)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h
  exact h

lemma sum_vanishes (P : Matrix (Joint S) (Joint S) ℝ) (i : Fin N) [Nonempty (S i)]
    (χ : S i → ℝ) (hχ : ∑ s : S i, χ s = 0)
    (K : Joint S → Joint S → ℝ)
    (hKa : ∀ (a b : Joint S) (s : S i), K (Function.update a i s) b = K a b)
    (hKb : ∀ (a b : Joint S) (t : S i), K a (Function.update b i t) = K a b)
    (hmarg : ∀ (a b : Joint S) (s : S i),
      ∑ t : S i, P (Function.update a i s) (Function.update b i t)
        = ∑ t : S i, P a (Function.update b i t)) :
    ∑ a : Joint S, ∑ b : Joint S, (χ (a i) * K a b) * P a b = 0 := by
  classical
  have hm : ((Fintype.card (S i) : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  set R : Joint S → Joint S → ℝ := fun a b => ∑ t : S i, P a (Function.update b i t) with hR
  have hRa : ∀ (a b : Joint S) (s : S i), R (Function.update a i s) b = R a b := by
    intro a b s; exact hmarg a b s
  have stepA : ∀ a : Joint S,
      (Fintype.card (S i) : ℝ) * (∑ b : Joint S, K a b * P a b) = ∑ b : Joint S, K a b * R a b := by
    intro a
    have h := sum_coordSwap (S := S) i (fun c _u => K a c * P a c)
    have hL : ∑ b : Joint S, ∑ _t : S i, K a (Function.update b i _t) * P a (Function.update b i _t)
        = ∑ b : Joint S, K a b * R a b := by
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hR]
      simp only [hKb a b, ← Finset.mul_sum]
    have hRr : ∑ c : Joint S, ∑ _u : S i, K a c * P a c
        = (Fintype.card (S i) : ℝ) * ∑ c : Joint S, K a c * P a c := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hL, hRr] at h
    exact h.symm
  have stepB : ∑ a : Joint S, χ (a i) * (∑ b : Joint S, K a b * R a b) = 0 := by
    have h := sum_coordSwap (S := S) i (fun c u => χ u * ∑ b : Joint S, K c b * R c b)
    have hL : ∑ a : Joint S, ∑ _s : S i,
          χ (a i) * ∑ b : Joint S, K (Function.update a i _s) b * R (Function.update a i _s) b
        = (Fintype.card (S i) : ℝ) * ∑ a : Joint S, χ (a i) * ∑ b : Joint S, K a b * R a b := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have : ∀ s : S i,
          χ (a i) * ∑ b : Joint S, K (Function.update a i s) b * R (Function.update a i s) b
            = χ (a i) * ∑ b : Joint S, K a b * R a b := by
        intro s
        congr 1
        exact Finset.sum_congr rfl fun b _ => by rw [hKa a b s, hRa a b s]
      rw [Finset.sum_congr rfl fun s _ => this s, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
    have hRr : ∑ c : Joint S, ∑ u : S i, χ u * ∑ b : Joint S, K c b * R c b = 0 := by
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [← Finset.sum_mul, hχ, zero_mul]
    rw [hL, hRr] at h
    exact (mul_eq_zero.mp h).resolve_left hm
  have final : ∀ a : Joint S, ∑ b : Joint S, (χ (a i) * K a b) * P a b
      = χ (a i) * ((Fintype.card (S i) : ℝ))⁻¹ * ∑ b : Joint S, K a b * R a b := by
    intro a
    have h1 : ∑ b : Joint S, (χ (a i) * K a b) * P a b
        = χ (a i) * ∑ b : Joint S, K a b * P a b := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    have h2 : ∑ b : Joint S, K a b * P a b
        = ((Fintype.card (S i) : ℝ))⁻¹ * ∑ b : Joint S, K a b * R a b := by
      rw [← stepA a, ← mul_assoc, inv_mul_cancel₀ hm, one_mul]
    rw [h1, h2, ← mul_assoc]
  rw [Finset.sum_congr rfl fun a _ => final a]
  have : ∑ a : Joint S, χ (a i) * ((Fintype.card (S i) : ℝ))⁻¹ * ∑ b : Joint S, K a b * R a b
      = ((Fintype.card (S i) : ℝ))⁻¹
        * ∑ a : Joint S, χ (a i) * ∑ b : Joint S, K a b * R a b := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [this, stepB, mul_zero]

/-! ### Part 8. Assembly -/

/-- **The separability criterion.**  If, for every agent `i`, summing the joint transition over
agent `i`'s next state leaves a quantity that no longer sees agent `i`'s current state, then the
joint transition is separable. -/
theorem agentwise_marginal_independence_implies_separable
    (P : Matrix (Joint S) (Joint S) ℝ) (hP : IsTransitionMatrix P)
    (hmarg0 : ∀ (i : Fin N) (p p' q : Joint S), (∀ j, j ≠ i → p j = p' j) →
      ∑ t : S i, P p (Function.update q i t) = ∑ t : S i, P p' (Function.update q i t)) :
    IsSeparableN P := by
  classical
  rcases isEmpty_or_nonempty (Joint S) with hE | hNE
  · refine ⟨1, fun _ => 1, fun _ i => fun _ _ => 1 / (Fintype.card (S i) : ℝ), ?_, by simp, ?_⟩
    · intro k i
      refine ⟨fun a b => by positivity, fun a => ?_⟩
      have hpos : 0 < Fintype.card (S i) := Fintype.card_pos_iff.mpr ⟨a⟩
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div,
        div_self (Nat.cast_ne_zero.mpr hpos.ne')]
    · funext p q; exact (IsEmpty.false p).elim
  obtain ⟨o⟩ := hNE
  haveI hSne : ∀ i, Nonempty (S i) := fun i => ⟨o i⟩
  have hmarg : ∀ (i : Fin N) (a b : Joint S) (s : S i),
      ∑ t : S i, P (Function.update a i s) (Function.update b i t)
        = ∑ t : S i, P a (Function.update b i t) := by
    intro i a b s
    exact hmarg0 i _ a b (fun j hj => Function.update_of_ne hj s a)
  have hvanish : ∀ x : SepIdx S, (∃ (i : Fin N) (s : S i), x i = Sum.inr s)
      → sepCoef P o x = 0 := by
    rintro x ⟨i, s, hxi⟩
    have hdual : ∀ a b : Joint S, resDual (o i) (x i) (a i) (b i)
        = (fun y : S i => (if y = s then (1 : ℝ) else 0)
            - 1 / (Fintype.card (S i) : ℝ)) (a i) := by
      intro a b; rw [hxi]; rfl
    have hχ : ∑ y : S i, ((if y = s then (1 : ℝ) else 0)
        - 1 / (Fintype.card (S i) : ℝ)) = 0 := sum_resDual_inr (o i) s (o i)
    have hKa : ∀ (a b : Joint S) (t : S i),
        (∏ j ∈ Finset.univ.erase i, resDual (o j) (x j) ((Function.update a i t) j) (b j))
          = ∏ j ∈ Finset.univ.erase i, resDual (o j) (x j) (a j) (b j) := by
      intro a b t
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
    have hKb : ∀ (a b : Joint S) (t : S i),
        (∏ j ∈ Finset.univ.erase i, resDual (o j) (x j) (a j) ((Function.update b i t) j))
          = ∏ j ∈ Finset.univ.erase i, resDual (o j) (x j) (a j) (b j) := by
      intro a b t
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
    have hprod : ∀ a b : Joint S,
        (∏ j, resDual (o j) (x j) (a j) (b j)) * P a b
          = (((if a i = s then (1 : ℝ) else 0) - 1 / (Fintype.card (S i) : ℝ))
              * ∏ j ∈ Finset.univ.erase i, resDual (o j) (x j) (a j) (b j)) * P a b := by
      intro a b
      rw [← Finset.mul_prod_erase Finset.univ (fun j => resDual (o j) (x j) (a j) (b j))
        (Finset.mem_univ i), hdual a b]
    simp only [sepCoef]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hprod a b]
    exact sum_vanishes P i
      (fun y : S i => (if y = s then (1 : ℝ) else 0) - 1 / (Fintype.card (S i) : ℝ)) hχ
      (fun a b => ∏ j ∈ Finset.univ.erase i, resDual (o j) (x j) (a j) (b j))
      hKa hKb (hmarg i)
  have hPq : ∀ p q : Joint S, P p q
      = ∑ x : SepIdx S, sepCoef P o x * ∏ i, goodVec (o i) (x i) (p i) (q i) := by
    intro p q
    rw [sep_expansion P o p q]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : ∃ (i : Fin N) (s : S i), x i = Sum.inr s
    · rw [hvanish x hx, zero_mul, zero_mul]
    · push_neg at hx
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rcases hxi : x i with st | s
      · rfl
      · exact absurd hxi (hx i s)
  refine ⟨Fintype.card (SepIdx S),
    fun k => sepCoef P o ((Fintype.equivFin (SepIdx S)).symm k),
    fun k i => goodVec (o i) (((Fintype.equivFin (SepIdx S)).symm k) i), ?_, ?_, ?_⟩
  · intro k i; exact goodVec_isTransition (o i) _
  · rw [Equiv.sum_comp (Fintype.equivFin (SepIdx S)).symm (fun x => sepCoef P o x)]
    have h2 : ∑ q : Joint S, P o q = ∑ x : SepIdx S, sepCoef P o x := by
      rw [Finset.sum_congr rfl fun q _ => hPq o q, Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.mul_sum, sum_prod_eq_one (fun i => goodVec (o i) (x i))
        (fun i => goodVec_isTransition (o i) (x i)) o, mul_one]
    rw [← h2]
    exact hP.2 o
  · funext p q
    rw [hPq p q]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, tensorProdN]
    exact (Equiv.sum_comp (Fintype.equivFin (SepIdx S)).symm
      (fun x => sepCoef P o x * ∏ i, goodVec (o i) (x i) (p i) (q i))).symm

end MarkovEntanglement

open MarkovEntanglement in
theorem solution
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (hP : IsTransitionMatrix P)
    (hmarg : ∀ (i : Fin N) (p p' q : Joint S), (∀ j, j ≠ i → p j = p' j) →
      ∑ t : S i, P p (Function.update q i t) = ∑ t : S i, P p' (Function.update q i t)) :
    IsSeparableN P :=
  MarkovEntanglement.agentwise_marginal_independence_implies_separable P hP hmarg
