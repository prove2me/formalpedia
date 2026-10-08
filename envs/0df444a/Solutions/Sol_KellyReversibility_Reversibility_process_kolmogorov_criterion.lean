-- Prove2me | solution 1 for KellyReversibility.Reversibility.process_kolmogorov_criterion
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-07T22:47:43.642781+00:00
-- url     : https://prove2.me/submissions/94012ee9-15a4-4a51-98fd-4eda9c7800e4

-- SPDX-License-Identifier: Apache-2.0
-- Complete proof of Prove2Me 4de6143f-f77d-4ce8-8564-85f0e5169ca4.
-- Reused accepted contributions are attributed beside their full proof bodies.
import Definitions.Def_KellyReversibility_Reversibility_MarkovProcess
import Definitions.Def_KellyReversibility_Reversibility_StationaryLaw
import Definitions.Def_SerfozoStochasticNetworks_Reversible
import Mathlib

set_option autoImplicit false


-- BEGIN MODULE LawWeights
section

set_option autoImplicit false

namespace KellyReversibility.Reversibility.Proof

variable {S : Type*} {n : ℕ}

noncomputable def pathWeight (T : ℝ → Matrix S S ℝ) (π : S → ℝ)
    (t : Fin (n + 1) → ℝ) (j : Fin (n + 1) → S) : ℝ :=
  π (j 0) * ∏ r : Fin n, T (t r.succ - t r.castSucc) (j r.castSucc) (j r.succ)

lemma pathWeight_balance (T : ℝ → Matrix S S ℝ) (π : S → ℝ)
    (hπ : ∀ j, π j ≠ 0) (hdb : ∀ t j k, π j * T t j k = π k * T t k j)
    (t : Fin (n + 1) → ℝ) (j : Fin (n + 1) → S) :
    pathWeight T π t j =
      π (j (Fin.last n)) * ∏ r : Fin n, T (t r.succ - t r.castSucc) (j r.succ) (j r.castSucc) := by
  have he := Finset.prod_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun (r : Fin n) _ => hdb (t r.succ - t r.castSucc) (j r.castSucc) (j r.succ))
  simp only [Finset.prod_mul_distrib] at he
  have hp : π (j 0) * (∏ r : Fin n, π (j r.succ)) =
      (∏ r : Fin n, π (j r.castSucc)) * π (j (Fin.last n)) := by
    exact (Fin.prod_univ_succ (fun r => π (j r))).symm.trans
      (Fin.prod_univ_castSucc (fun r => π (j r)))
  have hn : (∏ r : Fin n, π (j r.castSucc)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun r _ => hπ _)
  apply mul_left_cancel₀ hn
  unfold pathWeight
  calc
    (∏ r : Fin n, π (j r.castSucc)) * (π (j 0) *
        ∏ r : Fin n, T (t r.succ - t r.castSucc) (j r.castSucc) (j r.succ))
      = π (j 0) * ((∏ r : Fin n, π (j r.castSucc)) *
          ∏ r : Fin n, T (t r.succ - t r.castSucc) (j r.castSucc) (j r.succ)) := by ring
    _ = π (j 0) * ((∏ r : Fin n, π (j r.succ)) *
          ∏ r : Fin n, T (t r.succ - t r.castSucc) (j r.succ) (j r.castSucc)) := by rw [he]
    _ = (π (j 0) * ∏ r : Fin n, π (j r.succ)) *
          ∏ r : Fin n, T (t r.succ - t r.castSucc) (j r.succ) (j r.castSucc) := by ring
    _ = (∏ r : Fin n, π (j r.castSucc)) * (π (j (Fin.last n)) *
          ∏ r : Fin n, T (t r.succ - t r.castSucc) (j r.succ) (j r.castSucc)) := by rw [hp]; ring

lemma pathWeight_time_reverse (T : ℝ → Matrix S S ℝ) (π : S → ℝ)
    (hπ : ∀ j, π j ≠ 0) (hdb : ∀ t j k, π j * T t j k = π k * T t k j)
    (t : Fin (n + 1) → ℝ) (j : Fin (n + 1) → S) (τ : ℝ) :
    pathWeight T π t j = pathWeight T π (fun r => τ - t r.rev) (fun r => j r.rev) := by
  rw [pathWeight_balance T π hπ hdb]
  unfold pathWeight
  simp only [Fin.rev_zero, Fin.rev_succ, Fin.rev_castSucc, sub_sub_sub_cancel_left]
  congr 1
  exact (Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin n))
    (fun (r : Fin n) => T (t r.succ - t r.castSucc) (j r.succ) (j r.castSucc))).symm

end KellyReversibility.Reversibility.Proof
end
-- END MODULE LawWeights

-- BEGIN MODULE LawSort
section

set_option autoImplicit false

namespace KellyReversibility.Reversibility.Proof

variable {S : Type*} [DecidableEq S] {n : ℕ}

lemma pathWeight_tied_adjacent (T : ℝ → Matrix S S ℝ) (π : S → ℝ)
    (hT : T 0 = 1) (t : Fin (n+1) → ℝ) (j : Fin (n+1) → S)
    (hw : pathWeight T π t j ≠ 0) (i : Fin n) (ht : t i.castSucc = t i.succ) :
    j i.castSucc = j i.succ := by
  have hp : (∏ r : Fin n, T (t r.succ - t r.castSucc) (j r.castSucc) (j r.succ)) ≠ 0 :=
    (mul_ne_zero_iff.mp hw).2
  have hi := (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ _)
  rw [ht, sub_self, hT] at hi
  by_contra hne
  exact hi (Matrix.one_apply_ne hne)

lemma pathWeight_tied_states (T : ℝ → Matrix S S ℝ) (π : S → ℝ)
    (hT : T 0 = 1) (t : Fin (n+1) → ℝ) (j : Fin (n+1) → S)
    (hmono : Monotone t) (hw : pathWeight T π t j ≠ 0)
    (a b : Fin (n+1)) (ht : t a = t b) : j a = j b := by
  have hordered : ∀ (b a : Fin (n+1)), a ≤ b → t a = t b → j a = j b := by
    intro b
    induction b using Fin.induction with
    | zero =>
      intro a ha _
      have he : a = 0 := Fin.le_zero_iff.mp ha
      rw [he]
    | succ b ih =>
      intro a ha hab
      by_cases he : a = b.succ
      · rw [he]
      have hab' : a ≤ b.castSucc := by
        have ha' := ha
        simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc] at ha' ⊢
        have hh : a.val ≠ b.val + 1 := by
          intro hh
          exact he (Fin.ext hh)
        omega
      have hmid : t b.castSucc = t b.succ := by
        apply le_antisymm (hmono b.castSucc_le_succ)
        rw [← hab]
        exact hmono hab'
      exact (ih a hab' (hab.trans hmid.symm)).trans
        (pathWeight_tied_adjacent T π hT t j hw b hmid)
  rcases le_total a b with hab | hba
  · exact hordered b a hab ht
  · exact (hordered a b hba ht.symm).symm

lemma pathWeight_sorted_eq_of_ne_zero (T : ℝ → Matrix S S ℝ) (π : S → ℝ)
    (hT : T 0 = 1) (t : Fin (n+1) → ℝ) (j : Fin (n+1) → S)
    (σ τ : Equiv.Perm (Fin (n+1)))
    (hσ : Monotone (t ∘ σ)) (hτ : Monotone (t ∘ τ))
    (hw : pathWeight T π (t ∘ σ) (j ∘ σ) ≠ 0) :
    pathWeight T π (t ∘ σ) (j ∘ σ) = pathWeight T π (t ∘ τ) (j ∘ τ) := by
  have ht : t ∘ σ = t ∘ τ := Tuple.unique_monotone hσ hτ
  have hj : j ∘ σ = j ∘ τ := by
    funext r
    have he : (t ∘ σ) r = (t ∘ σ) (σ.symm (τ r)) := by
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using congrFun ht r
    have hh := pathWeight_tied_states T π hT (t ∘ σ) (j ∘ σ) hσ hw
      r (σ.symm (τ r)) he
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hh
  rw [ht, hj]

lemma pathWeight_sorted_eq (T : ℝ → Matrix S S ℝ) (π : S → ℝ)
    (hT : T 0 = 1) (t : Fin (n+1) → ℝ) (j : Fin (n+1) → S)
    (σ τ : Equiv.Perm (Fin (n+1)))
    (hσ : Monotone (t ∘ σ)) (hτ : Monotone (t ∘ τ)) :
    pathWeight T π (t ∘ σ) (j ∘ σ) = pathWeight T π (t ∘ τ) (j ∘ τ) := by
  by_cases hs : pathWeight T π (t ∘ σ) (j ∘ σ) ≠ 0
  · exact pathWeight_sorted_eq_of_ne_zero T π hT t j σ τ hσ hτ hs
  by_cases ht : pathWeight T π (t ∘ τ) (j ∘ τ) ≠ 0
  · exact (pathWeight_sorted_eq_of_ne_zero T π hT t j τ σ hτ hσ ht).symm
  push Not at hs ht
  rw [hs, ht]

end KellyReversibility.Reversibility.Proof

end
-- END MODULE LawSort

-- BEGIN MODULE TwoTimeBalance
section

set_option autoImplicit false

open scoped Matrix.Norms.Operator

namespace KellyReversibility.Reversibility.Proof

variable {S : Type*} [Fintype S] [DecidableEq S]

lemma sort_two_increasing (t : ℝ) (ht : 0 ≤ t) :
    Tuple.sort ![0, t] = Equiv.refl (Fin 2) := by
  apply Tuple.sort_eq_refl_iff_monotone.mpr
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

lemma sort_two_decreasing (t : ℝ) (ht : 0 < t) :
    Tuple.sort ![t, 0] = Equiv.swap (0 : Fin 2) 1 := by
  symm
  apply Tuple.eq_sort_iff.mpr
  constructor
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all; linarith
  · intro a b hab he
    fin_cases a <;> fin_cases b <;> simp_all

lemma transition_zero (q : S → S → ℝ) : transition q 0 = 1 := by
  simp [transition]

lemma transition_hasDerivAt_zero (q : S → S → ℝ) (j k : S) :
    HasDerivAt (fun t : ℝ => transition q t j k) (generator q j k) 0 := by
  have hh := hasDerivAt_exp_smul_const (generator q) (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at hh
  exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hh j) k

lemma transition_balance_of_reversible (q : S → S → ℝ) (π : S → ℝ)
    (hr : ProcessReversible q π) (t : ℝ) (ht : 0 ≤ t) (j k : S) :
    π j * transition q t j k = π k * transition q t k j := by
  by_cases ht0 : t = 0
  · subst t
    rw [transition_zero]
    by_cases hjk : j = k
    · subst k; rfl
    · simp [hjk, Ne.symm hjk]
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have h := hr 1 ![0, t] ![j, k] t
  have he : (fun r : Fin 2 => t - ![0, t] r) = ![t, 0] := by
    funext r; fin_cases r <;> simp
  rw [he] at h
  simpa [fdd, sort_two_increasing t ht, sort_two_decreasing t htp] using h

lemma detailedBalance_of_processReversible (q : S → S → ℝ) (π : S → ℝ)
    (hr : ProcessReversible q π) : KellyStochasticNetworks.DetailedBalance π q := by
  intro j k
  by_cases hjk : j = k
  · subst k; rfl
  have h1 := ((transition_hasDerivAt_zero q j k).const_mul (π j)).hasDerivWithinAt (s := Set.Ici 0)
  have h2 := ((transition_hasDerivAt_zero q k j).const_mul (π k)).hasDerivWithinAt (s := Set.Ici 0)
  have he : Set.EqOn (fun t => π j * transition q t j k)
      (fun t => π k * transition q t k j) (Set.Ici 0) :=
    fun t ht => transition_balance_of_reversible q π hr t ht j k
  have hh := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ h1
    (h2.congr he (he (by simp)))
  simpa [generator, Matrix.sub_apply, Matrix.diagonal_apply, hjk, Ne.symm hjk] using hh

end KellyReversibility.Reversibility.Proof

end
-- END MODULE TwoTimeBalance

-- BEGIN MODULE TransitionBalance
section

set_option autoImplicit false

open scoped Matrix.Norms.Operator

namespace KellyReversibility.Reversibility.Proof

variable {S : Type*} [Fintype S] [DecidableEq S]

lemma generator_balance (q : S → S → ℝ) (π : S → ℝ)
    (hdb : KellyStochasticNetworks.DetailedBalance π q) :
    KellyStochasticNetworks.DetailedBalance π (generator q) := by
  intro j k
  by_cases hjk : j = k
  · subst k; rfl
  simpa [generator, Matrix.diagonal_apply, hjk, Ne.symm hjk] using hdb j k

lemma transition_balance (q : S → S → ℝ) (π : S → ℝ)
    (hdb : KellyStochasticNetworks.DetailedBalance π q) (t : ℝ) :
    KellyStochasticNetworks.DetailedBalance π (transition q t) := by
  have hg := generator_balance q π hdb
  have hsem : SemiconjBy (Matrix.diagonal π) (t • generator q) (t • (generator q).transpose) := by
    ext j k
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply,
      Matrix.transpose_apply, smul_eq_mul]
    calc π j * (t * generator q j k) = t * (π j * generator q j k) := by ring
      _ = t * (π k * generator q k j) := by rw [hg j k]
      _ = t * generator q k j * π k := by ring
  have hexp := hsem.exp_right
  intro j k
  have hh := congrArg (fun A : Matrix S S ℝ => A j k) hexp.eq
  have he : NormedSpace.exp (t • (generator q).transpose) =
      (NormedSpace.exp (t • generator q)).transpose := Matrix.exp_transpose _
  erw [he] at hh
  simpa [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply, transition, mul_comm] using! hh

end KellyReversibility.Reversibility.Proof

end
-- END MODULE TransitionBalance

-- BEGIN MODULE LawReversal
section

set_option autoImplicit false

namespace KellyReversibility.Reversibility.Proof

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem processReversible_of_detailedBalance (q : S → S → ℝ) (π : S → ℝ)
    (hπ : ∀ j, π j ≠ 0) (hdb : KellyStochasticNetworks.DetailedBalance π q) :
    ProcessReversible q π := by
  intro n t j τ
  have hm : Monotone ((fun r => τ - t r) ∘
      (Fin.revPerm.trans (Tuple.sort t))) := by
    intro a b hab
    apply sub_le_sub_left
    exact Tuple.monotone_sort t (Fin.rev_le_rev.mpr hab)
  have hs := pathWeight_sorted_eq (transition q) π (transition_zero q)
    (fun r => τ - t r) j (Fin.revPerm.trans (Tuple.sort t))
    (Tuple.sort (fun r => τ - t r)) hm (Tuple.monotone_sort _)
  calc
    fdd (transition q) π t j = pathWeight (transition q) π (t ∘ Tuple.sort t) (j ∘ Tuple.sort t) := rfl
    _ = pathWeight (transition q) π (fun r => τ - (t ∘ Tuple.sort t) r.rev)
        (fun r => (j ∘ Tuple.sort t) r.rev) :=
      pathWeight_time_reverse (transition q) π hπ (transition_balance q π hdb) _ _ τ
    _ = pathWeight (transition q) π ((fun r => τ - t r) ∘ Tuple.sort (fun r => τ - t r))
        (j ∘ Tuple.sort (fun r => τ - t r)) := hs
    _ = fdd (transition q) π (fun r => τ - t r) j := rfl

end KellyReversibility.Reversibility.Proof

end
-- END MODULE LawReversal

-- BEGIN MODULE AttributedSerfozo
section
-- Prove2me | solution 1 for SerfozoStochasticNetworks.kolmogorov_criterion
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T23:20:45.733981+00:00
-- url     : https://prove2.me/submissions/a33deca2-ef6c-4501-b4e3-ab79a580810a


namespace SerfozoStochasticNetworks

open Finset

variable {E : Type*}

/-- A tuple `p₀, …, p_n` read as a sequence on `ℕ` (constant after `p_n`). -/
def kcSeq {n : ℕ} (p : Fin (n + 1) → E) (k : ℕ) : E :=
  if h : k ≤ n then p ⟨k, Nat.lt_succ_of_le h⟩ else p (Fin.last n)

lemma kcSeq_val {n : ℕ} (p : Fin (n + 1) → E) (i : Fin (n + 1)) : kcSeq p i = p i := by
  unfold kcSeq
  rw [dif_pos (Nat.lt_succ_iff.mp i.isLt)]

lemma kcSeq_zero {n : ℕ} (p : Fin (n + 1) → E) : kcSeq p 0 = p 0 := by
  simpa using kcSeq_val p 0

lemma kcSeq_last {n : ℕ} (p : Fin (n + 1) → E) : kcSeq p n = p (Fin.last n) :=
  kcSeq_val p (Fin.last n)

/-- Products along a tuple as products over `range`. -/
lemma kc_prod {n : ℕ} (p : Fin (n + 1) → E) (g : E → E → ℝ) :
    ∏ i : Fin n, g (p i.castSucc) (p i.succ) =
      ∏ k ∈ range n, g (kcSeq p k) (kcSeq p (k + 1)) := by
  rw [← Fin.prod_univ_eq_prod_range (fun k => g (kcSeq p k) (kcSeq p (k + 1))) n]
  refine prod_congr rfl fun i _ => ?_
  have h1 : kcSeq p (i : ℕ) = p i.castSucc := kcSeq_val p i.castSucc
  have h2 : kcSeq p ((i : ℕ) + 1) = p i.succ := kcSeq_val p i.succ
  show _ = g (kcSeq p (i : ℕ)) (kcSeq p ((i : ℕ) + 1))
  rw [h1, h2]

/-- Products along the tuple of a sequence. -/
lemma kc_tup_prod (C : ℕ → E) (N : ℕ) (g : E → E → ℝ) :
    ∏ i : Fin N, g (C (i.castSucc : Fin (N + 1))) (C (i.succ : Fin (N + 1))) =
      ∏ k ∈ range N, g (C k) (C (k + 1)) :=
  Fin.prod_univ_eq_prod_range (fun k => g (C k) (C (k + 1))) N

lemma kc_path_seq (q : E → E → ℝ) {n : ℕ} (p : Fin (n + 1) → E) (hp : IsPath q p) :
    ∀ k < n, 0 < q (kcSeq p k) (kcSeq p (k + 1)) := by
  intro k hk
  have h1 : kcSeq p k = p (Fin.castSucc ⟨k, hk⟩) := kcSeq_val p (Fin.castSucc ⟨k, hk⟩)
  have h2 : kcSeq p (k + 1) = p (Fin.succ ⟨k, hk⟩) := kcSeq_val p (Fin.succ ⟨k, hk⟩)
  rw [h1, h2]
  exact hp ⟨k, hk⟩

lemma kc_seq_path (q : E → E → ℝ) (C : ℕ → E) (N : ℕ)
    (h : ∀ k < N, 0 < q (C k) (C (k + 1))) : IsPath q (fun i : Fin (N + 1) => C i) :=
  fun i => h i i.isLt

lemma kc_ratio_pos (q : E → E → ℝ) (htw : TwoWay q) {n : ℕ} (p : Fin (n + 1) → E)
    (hp : IsPath q p) : 0 < pathRatio q p :=
  prod_pos fun i _ => div_pos (hp i) ((htw _ _).mp (hp i))

/-- Detailed balance gives Kolmogorov's criterion on every closed sequence of states. -/
lemma kc_rev_kol (q : E → E → ℝ) (h : IsReversible q) : KolmogorovCriterion q := by
  obtain ⟨π, hπ, hdb⟩ := h
  intro n p hp
  have e1 : pathRate q p = ∏ k ∈ range n, q (kcSeq p k) (kcSeq p (k + 1)) := kc_prod p q
  have e2 : pathRateRev q p = ∏ k ∈ range n, q (kcSeq p (k + 1)) (kcSeq p k) :=
    kc_prod p (fun a b => q b a)
  rw [e1, e2]
  have hP : kcSeq p 0 = kcSeq p n := by rw [kcSeq_zero, kcSeq_last, hp]
  have key : (∏ k ∈ range n, π (kcSeq p k)) * ∏ k ∈ range n, q (kcSeq p k) (kcSeq p (k + 1)) =
      (∏ k ∈ range n, π (kcSeq p (k + 1))) * ∏ k ∈ range n, q (kcSeq p (k + 1)) (kcSeq p k) := by
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    exact prod_congr rfl fun k _ => hdb _ _
  have hsame : ∏ k ∈ range n, π (kcSeq p k) = ∏ k ∈ range n, π (kcSeq p (k + 1)) := by
    have f1 : ∏ k ∈ range (n + 1), π (kcSeq p k) =
        (∏ k ∈ range n, π (kcSeq p k)) * π (kcSeq p n) := prod_range_succ _ _
    have f2 : ∏ k ∈ range (n + 1), π (kcSeq p k) =
        (∏ k ∈ range n, π (kcSeq p (k + 1))) * π (kcSeq p 0) := prod_range_succ' _ _
    rw [f1, hP] at f2
    exact mul_right_cancel₀ (hπ _).ne' f2
  have hpos : 0 < ∏ k ∈ range n, π (kcSeq p (k + 1)) := prod_pos fun k _ => hπ _
  rw [hsame] at key
  exact mul_left_cancel₀ hpos.ne' key

/-- The reversal of `p'` followed by `p`, as a sequence on `ℕ`. -/
def kcJoin {n n' : ℕ} (p : Fin (n + 1) → E) (p' : Fin (n' + 1) → E) (i : ℕ) : E :=
  if i ≤ n' then kcSeq p' (n' - i) else kcSeq p (i - n')

lemma kcJoin_add {n n' : ℕ} (p : Fin (n + 1) → E) (p' : Fin (n' + 1) → E) (h0 : p 0 = p' 0)
    (k : ℕ) : kcJoin p p' (n' + k) = kcSeq p k := by
  unfold kcJoin
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Nat.add_zero, if_pos le_rfl, Nat.sub_self, kcSeq_zero, kcSeq_zero, h0]
  · rw [if_neg (show ¬ (n' + k ≤ n') by omega), Nat.add_sub_cancel_left]

lemma kc_reflect (P' : ℕ → E) (n' : ℕ) (g : E → E → ℝ) :
    ∏ k ∈ range n', g (P' (n' - k)) (P' (n' - (k + 1))) =
      ∏ j ∈ range n', g (P' (j + 1)) (P' j) := by
  have h := prod_range_reflect (fun j => g (P' (j + 1)) (P' j)) n'
  have h' : ∏ j ∈ range n', g (P' (n' - 1 - j + 1)) (P' (n' - 1 - j)) =
      ∏ j ∈ range n', g (P' (j + 1)) (P' j) := h
  rw [← h']
  refine prod_congr rfl fun k hk => ?_
  have hk' := mem_range.mp hk
  have e1 : n' - 1 - k + 1 = n' - k := by omega
  have e2 : n' - 1 - k = n' - (k + 1) := by omega
  rw [e1, e2]

lemma kc_join_prod {n n' : ℕ} (p : Fin (n + 1) → E) (p' : Fin (n' + 1) → E) (h0 : p 0 = p' 0)
    (g : E → E → ℝ) :
    ∏ k ∈ range (n' + n), g (kcJoin p p' k) (kcJoin p p' (k + 1)) =
      (∏ j ∈ range n', g (kcSeq p' (j + 1)) (kcSeq p' j)) *
        ∏ k ∈ range n, g (kcSeq p k) (kcSeq p (k + 1)) := by
  rw [prod_range_add, ← kc_reflect (kcSeq p') n' g]
  congr 1
  · refine prod_congr rfl fun k hk => ?_
    have hk' := mem_range.mp hk
    unfold kcJoin
    rw [if_pos (show k ≤ n' by omega), if_pos (show k + 1 ≤ n' by omega)]
  · refine prod_congr rfl fun k _ => ?_
    have h1 := kcJoin_add p p' h0 k
    have h2 : kcJoin p p' (n' + k + 1) = kcSeq p (k + 1) := kcJoin_add p p' h0 (k + 1)
    rw [h1, h2]

/-- Kolmogorov's criterion gives the invariance of the ratio products along paths. -/
lemma kc_kol_ri (q : E → E → ℝ) (htw : TwoWay q) (h : KolmogorovCriterion q) :
    RatioInvariance q := by
  intro n n' p p' hp hp' h0 hl
  have hcl : kcJoin p p' 0 = kcJoin p p' (n' + n) := by
    rw [kcJoin_add p p' h0 n, kcSeq_last, hl]
    unfold kcJoin
    rw [if_pos (Nat.zero_le _), Nat.sub_zero, kcSeq_last]
  have hK := h (n' + n) (fun i => kcJoin p p' i) (by simpa using hcl)
  have e1 : pathRate q (fun i : Fin (n' + n + 1) => kcJoin p p' i) =
      ∏ k ∈ range (n' + n), q (kcJoin p p' k) (kcJoin p p' (k + 1)) :=
    kc_tup_prod (kcJoin p p') (n' + n) q
  have e2 : pathRateRev q (fun i : Fin (n' + n + 1) => kcJoin p p' i) =
      ∏ k ∈ range (n' + n), q (kcJoin p p' (k + 1)) (kcJoin p p' k) :=
    kc_tup_prod (kcJoin p p') (n' + n) (fun a b => q b a)
  have e4 : ∏ k ∈ range (n' + n), q (kcJoin p p' (k + 1)) (kcJoin p p' k) =
      (∏ j ∈ range n', q (kcSeq p' j) (kcSeq p' (j + 1))) *
        ∏ k ∈ range n, q (kcSeq p (k + 1)) (kcSeq p k) :=
    kc_join_prod p p' h0 (fun a b => q b a)
  rw [e1, e2, kc_join_prod p p' h0 q, e4] at hK
  have r1 : pathRatio q p = (∏ k ∈ range n, q (kcSeq p k) (kcSeq p (k + 1))) /
      ∏ k ∈ range n, q (kcSeq p (k + 1)) (kcSeq p k) := by
    rw [← prod_div_distrib]; exact kc_prod p (fun a b => q a b / q b a)
  have r2 : pathRatio q p' = (∏ k ∈ range n', q (kcSeq p' k) (kcSeq p' (k + 1))) /
      ∏ k ∈ range n', q (kcSeq p' (k + 1)) (kcSeq p' k) := by
    rw [← prod_div_distrib]; exact kc_prod p' (fun a b => q a b / q b a)
  have hpos : 0 < ∏ k ∈ range n, q (kcSeq p (k + 1)) (kcSeq p k) :=
    prod_pos fun k hk => (htw _ _).mp (kc_path_seq q p hp k (mem_range.mp hk))
  have hpos' : 0 < ∏ k ∈ range n', q (kcSeq p' (k + 1)) (kcSeq p' k) :=
    prod_pos fun k hk => (htw _ _).mp (kc_path_seq q p' hp' k (mem_range.mp hk))
  rw [r1, r2, div_eq_div_iff hpos.ne' hpos'.ne', mul_comm]
  exact hK

/-- The sequence `p₀, …, p_n, y`. -/
def kcSnoc {n : ℕ} (p : Fin (n + 1) → E) (y : E) (k : ℕ) : E :=
  if k ≤ n then kcSeq p k else y

/-- Invariance of the ratio products yields a positive solution of detailed balance:
`π(x)` is the ratio product along any path from a fixed state to `x`. -/
lemma kc_ri_rev (q : E → E → ℝ) (hq : ∀ x y, 0 ≤ q x y) (htw : TwoWay q)
    (hirr : IsIrreducible q) (h : RatioInvariance q) : IsReversible q := by
  rcases isEmpty_or_nonempty E with hE | ⟨⟨x₀⟩⟩
  · exact ⟨fun _ => 1, fun x => isEmptyElim x, fun x => isEmptyElim x⟩
  choose N P hP hP0 hPl using fun x => hirr x₀ x
  refine ⟨fun x => pathRatio q (P x), fun x => kc_ratio_pos q htw (P x) (hP x), fun x y => ?_⟩
  show pathRatio q (P x) * q x y = pathRatio q (P y) * q y x
  rcases (hq x y).lt_or_eq with hxy | hxy
  · have hyx : 0 < q y x := (htw x y).mp hxy
    have hS : ∀ k ≤ N x, kcSnoc (P x) y k = kcSeq (P x) k := fun k hk => if_pos hk
    have hSx : kcSnoc (P x) y (N x) = x := by rw [hS _ le_rfl, kcSeq_last, hPl]
    have hSy : kcSnoc (P x) y (N x + 1) = y := if_neg (by omega)
    have hpath : IsPath q (fun i : Fin (N x + 1 + 1) => kcSnoc (P x) y i) := by
      refine kc_seq_path q _ _ fun k hk => ?_
      rcases Nat.lt_or_ge k (N x) with hk' | hk'
      · rw [hS k hk'.le, hS (k + 1) hk']
        exact kc_path_seq q (P x) (hP x) k hk'
      · have hkN : k = N x := by omega
        subst hkN
        rw [hSx, hSy]
        exact hxy
    have hratio : pathRatio q (fun i : Fin (N x + 1 + 1) => kcSnoc (P x) y i) =
        pathRatio q (P x) * (q x y / q y x) := by
      have e : pathRatio q (fun i : Fin (N x + 1 + 1) => kcSnoc (P x) y i) =
          ∏ k ∈ range (N x + 1), q (kcSnoc (P x) y k) (kcSnoc (P x) y (k + 1)) /
            q (kcSnoc (P x) y (k + 1)) (kcSnoc (P x) y k) :=
        kc_tup_prod (kcSnoc (P x) y) (N x + 1) (fun a b => q a b / q b a)
      have e' : pathRatio q (P x) =
          ∏ k ∈ range (N x), q (kcSeq (P x) k) (kcSeq (P x) (k + 1)) /
            q (kcSeq (P x) (k + 1)) (kcSeq (P x) k) :=
        kc_prod (P x) (fun a b => q a b / q b a)
      rw [e, e', prod_range_succ, hSx, hSy]
      congr 1
      refine prod_congr rfl fun k hk => ?_
      have hk' := mem_range.mp hk
      rw [hS k hk'.le, hS (k + 1) hk']
    have hRI := h (N x + 1) (N y) (fun i => kcSnoc (P x) y i) (P y) hpath (hP y)
      (by
        show kcSnoc (P x) y ((0 : Fin (N x + 1 + 1)) : ℕ) = P y 0
        rw [Fin.val_zero, hS 0 (Nat.zero_le _), kcSeq_zero, hP0, hP0])
      (by
        show kcSnoc (P x) y ((Fin.last (N x + 1)) : ℕ) = P y (Fin.last (N y))
        rw [Fin.val_last, hSy, hPl])
    rw [hratio] at hRI
    rw [← hRI]
    field_simp
  · have hyx : q y x = 0 := by
      rcases (hq y x).lt_or_eq with h' | h'
      · exact absurd ((htw y x).mp h') (by rw [← hxy]; exact lt_irrefl 0)
      · exact h'.symm
    rw [← hxy, hyx, mul_zero, mul_zero]

/-- A reversible `q` has, for every base state, the normalized detailed-balance solution given
by the ratio products along paths from the base state. -/
lemma kc_rev_norm (q : E → E → ℝ) (htw : TwoWay q) (h : IsReversible q) (x₀ : E) :
    ∃ π : E → ℝ, (∀ x, 0 < π x) ∧ π x₀ = 1 ∧ DetailedBalance q π ∧
      ∀ (n : ℕ) (p : Fin (n + 1) → E), IsPath q p → p 0 = x₀ →
        π (p (Fin.last n)) = pathRatio q p := by
  obtain ⟨π, hπ, hdb⟩ := h
  refine ⟨fun x => π x / π x₀, fun x => div_pos (hπ x) (hπ x₀), div_self (hπ x₀).ne',
    fun x y => ?_, fun n p hp h0 => ?_⟩
  · show π x / π x₀ * q x y = π y / π x₀ * q y x
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, hdb x y]
  · show π (p (Fin.last n)) / π x₀ = pathRatio q p
    have key : ∀ k ≤ n, π (kcSeq p k) = π (kcSeq p 0) *
        ∏ i ∈ range k, q (kcSeq p i) (kcSeq p (i + 1)) / q (kcSeq p (i + 1)) (kcSeq p i) := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        rw [prod_range_succ, ← mul_assoc, ← ih (by omega)]
        have hpos := kc_path_seq q p hp k (by omega)
        have hpos' := (htw _ _).mp hpos
        rw [← mul_div_assoc, hdb, mul_div_assoc, div_self hpos'.ne', mul_one]
    have e : pathRatio q p = ∏ i ∈ range n, q (kcSeq p i) (kcSeq p (i + 1)) /
        q (kcSeq p (i + 1)) (kcSeq p i) := kc_prod p (fun a b => q a b / q b a)
    rw [e, ← kcSeq_last p, key n le_rfl, kcSeq_zero, h0]
    field_simp [(hπ x₀).ne']

end SerfozoStochasticNetworks

open SerfozoStochasticNetworks

theorem checked_serfozo_kolmogorov {E : Type*} (q : E → E → ℝ)
    (hq : ∀ x y, 0 ≤ q x y) (htw : TwoWay q) (hirr : IsIrreducible q) :
    (IsReversible q ↔ KolmogorovCriterion q) ∧ (IsReversible q ↔ RatioInvariance q) ∧
    (IsReversible q → ∀ x₀ : E, ∃ π : E → ℝ, (∀ x, 0 < π x) ∧ π x₀ = 1 ∧ DetailedBalance q π ∧
      ∀ (n : ℕ) (p : Fin (n + 1) → E), IsPath q p → p 0 = x₀ →
        π (p (Fin.last n)) = pathRatio q p) :=
  ⟨⟨kc_rev_kol q, fun h => kc_ri_rev q hq htw hirr (kc_kol_ri q htw h)⟩,
    ⟨fun h => kc_kol_ri q htw (kc_rev_kol q h), kc_ri_rev q hq htw hirr⟩,
    fun h x₀ => kc_rev_norm q htw h x₀⟩

end
-- END MODULE AttributedSerfozo

-- BEGIN MODULE CycleBridge
section

set_option autoImplicit false

namespace KellyReversibility.Reversibility.Proof

open SerfozoStochasticNetworks

theorem reachable_path {S : Type*} (q : S → S → ℝ) {x y : S}
    (h : Relation.ReflTransGen (fun a b => 0 < q a b) x y) :
    ∃ n : ℕ, ∃ p : Fin (n+1) → S, IsPath q p ∧ p 0 = x ∧ p (Fin.last n) = y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, fun _ => y, (fun i => Fin.elim0 i), rfl, rfl⟩
  | @head a c hac h ih =>
    obtain ⟨n, p, hp, hp0, hpn⟩ := ih
    refine ⟨n+1, Fin.cons a p, ?_, rfl, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [hp0] using hac
      · simpa using hp j
    · simpa using hpn

theorem rates_irreducible_path {S : Type*} (q : S → S → ℝ) (h : RatesIrreducible q) :
    IsIrreducible q := fun x y => reachable_path q (h x y)

theorem closed_successor_eq {S : Type*} {n : ℕ} (p : Fin (n+1) → S)
    (hp : p 0 = p (Fin.last n)) (i : Fin n) :
    p i.succ = p (finRotate n i).castSucc := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [finRotate_last]
      exact hp.symm
    · have hr : finRotate (n+1) j.castSucc = j.succ := finRotate_of_lt j.isLt
      rw [hr]
      congr 1

theorem kelly_to_serfozo_cycle {S : Type*} (q : S → S → ℝ) (h : KolmogorovCycle q) :
    KolmogorovCriterion q := by
  intro n p hp
  have hh := h n (fun i => p i.castSucc)
  simpa only [pathRate, pathRateRev, ← closed_successor_eq p hp] using hh

theorem balance_to_kelly_cycle {S : Type*} (q : S → S → ℝ) (m : S → ℝ)
    (hm : ∀ j, 0 < m j) (hdb : KellyStochasticNetworks.DetailedBalance m q) :
    KolmogorovCycle q := by
  intro n j
  have hprod : (∏ i, m (j i)) * (∏ i, q (j i) (j (finRotate n i))) =
      (∏ i, m (j (finRotate n i))) * (∏ i, q (j (finRotate n i)) (j i)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => hdb _ _)
  rw [Equiv.prod_comp (finRotate n) (fun i => m (j i))] at hprod
  exact mul_left_cancel₀ (Finset.prod_pos (fun i _ => hm (j i))).ne' hprod

end KellyReversibility.Reversibility.Proof

end
-- END MODULE CycleBridge

-- BEGIN MODULE CycleBalance
section

set_option autoImplicit false

namespace KellyReversibility.Reversibility.Proof

open SerfozoStochasticNetworks

theorem cycle_twoWay {S : Type*} (q : S → S → ℝ)
    (hq : ∀ x y, 0 ≤ q x y) (hirr : RatesIrreducible q) (hc : KolmogorovCycle q) :
    TwoWay q := by
  have hk := kelly_to_serfozo_cycle q hc
  have one (x y : S) (hxy : 0 < q x y) : 0 < q y x := by
    obtain ⟨n, p, hp, hp0, hpn⟩ := reachable_path q (hirr y x)
    have hh := hk (n+1) (Fin.cons x p) (by simpa using hpn.symm)
    have hf : pathRate q (Fin.cons x p) = q x y * pathRate q p := by
      unfold pathRate
      rw [Fin.prod_univ_succ]
      simp [hp0]
    have hr : pathRateRev q (Fin.cons x p) = q y x * pathRateRev q p := by
      unfold pathRateRev
      rw [Fin.prod_univ_succ]
      simp [hp0]
    rw [hf, hr] at hh
    have hpos : 0 < q x y * pathRate q p :=
      mul_pos hxy (Finset.prod_pos (fun i _ => hp i))
    have hne : q y x ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hh
      exact (ne_of_gt hpos) hh
    exact lt_of_le_of_ne (hq y x) hne.symm
  exact fun x y => ⟨one x y, one y x⟩

theorem positive_balance_of_cycle {S : Type*} (q : S → S → ℝ)
    (hq : ∀ x y, 0 ≤ q x y) (hirr : RatesIrreducible q) (hc : KolmogorovCycle q) :
    ∃ m : S → ℝ, (∀ j, 0 < m j) ∧ KellyStochasticNetworks.DetailedBalance m q := by
  exact (checked_serfozo_kolmogorov q hq (cycle_twoWay q hq hirr hc)
    (rates_irreducible_path q hirr)).1.mpr (kelly_to_serfozo_cycle q hc)

end KellyReversibility.Reversibility.Proof

end
-- END MODULE CycleBalance

-- BEGIN MODULE EquilibriumBalance
section

set_option autoImplicit false

namespace KellyReversibility.Reversibility.Proof

theorem fullBalance_detailed_of_positive_balance {S : Type*} [Fintype S]
    (q : S → S → ℝ) (hq : ∀ j k, 0 ≤ q j k) (hirr : RatesIrreducible q)
    (m : S → ℝ) (hm : ∀ j, 0 < m j) (hdb : KellyStochasticNetworks.DetailedBalance m q)
    (π : S → ℝ) (hπ : KellyStochasticNetworks.FullBalance π q) :
    KellyStochasticNetworks.DetailedBalance π q := by
  classical
  cases isEmpty_or_nonempty S with
  | inl he => exact fun j => isEmptyElim j
  | inr he =>
    let r : S → ℝ := fun j => π j / m j
    have hr (j : S) : r j * m j = π j := div_mul_cancel₀ _ (hm j).ne'
    have hzero (j : S) : ∑ k, m j * q j k * (r j - r k) = 0 := by
      have ht (k : S) : m j * q j k * (r j - r k) = π j * q j k - π k * q k j := by
        calc
          _ = (r j * m j) * q j k - r k * (m j * q j k) := by ring
          _ = _ := by rw [hr j, hdb j k, ← mul_assoc, hr k]
      simp_rw [ht]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      exact sub_eq_zero.mpr (by simpa only [tsum_fintype] using hπ j)
    obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ r Finset.univ_nonempty
    have hmax (j : S) : r j ≤ r a := ha j (Finset.mem_univ _)
    have step (j k : S) (hj : r j = r a) (hjk : 0 < q j k) : r k = r a := by
      have hnonneg : ∀ k ∈ (Finset.univ : Finset S), 0 ≤ m j * q j k * (r j - r k) := by
        intro k _
        apply mul_nonneg (mul_nonneg (hm j).le (hq j k))
        rw [hj]
        exact sub_nonneg.mpr (hmax k)
      have hk := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp (hzero j) k (Finset.mem_univ _)
      have hdiff : r j - r k = 0 := (mul_eq_zero.mp hk).resolve_left (mul_pos (hm j) hjk).ne'
      exact (sub_eq_zero.mp hdiff).symm.trans hj
    have heq (j : S) : r j = r a := by
      have h := hirr a j
      induction h with
      | refl => rfl
      | @tail b c h hbc ih => exact step b c ih hbc
    intro j k
    calc
      π j * q j k = r a * (m j * q j k) := by rw [← hr j, heq j]; ring
      _ = r a * (m k * q k j) := congrArg (r a * ·) (hdb j k)
      _ = π k * q k j := by rw [← hr k, heq k]; ring

theorem equilibrium_detailed_of_cycle {S : Type*} [Fintype S]
    (q : S → S → ℝ) (hq : ∀ j k, j ≠ k → 0 ≤ q j k) (hq0 : ∀ j, q j j = 0)
    (hirr : RatesIrreducible q) (π : S → ℝ) (hπ : IsEquilibrium π q)
    (hc : KolmogorovCycle q) : KellyStochasticNetworks.DetailedBalance π q := by
  have hn (j k : S) : 0 ≤ q j k := by
    by_cases h : j = k
    · subst k; rw [hq0]
    · exact hq j k h
  obtain ⟨m, hm, hdb⟩ := positive_balance_of_cycle q hn hirr hc
  exact fullBalance_detailed_of_positive_balance q hn hirr m hm hdb π hπ.2.2

end KellyReversibility.Reversibility.Proof

end
-- END MODULE EquilibriumBalance

-- BEGIN MODULE ProcessKolmogorov
section

namespace KellyReversibility.Reversibility

/-- Theorem 1.8 (Kelly, p. 23). -/
theorem process_kolmogorov_criterion {S : Type*} [Fintype S] [DecidableEq S]
    (q : S → S → ℝ) (hq : ∀ j k, j ≠ k → 0 ≤ q j k) (hq0 : ∀ j, q j j = 0)
    (hirr : RatesIrreducible q)
    (π₀ : S → ℝ) (hπ₀ : IsEquilibrium π₀ q) :
    ProcessReversible q π₀ ↔ KolmogorovCycle q := by
  constructor
  · intro hr
    exact Proof.balance_to_kelly_cycle q π₀ hπ₀.1
      (Proof.detailedBalance_of_processReversible q π₀ hr)
  · intro hc
    exact Proof.processReversible_of_detailedBalance q π₀ (fun j => (hπ₀.1 j).ne')
      (Proof.equilibrium_detailed_of_cycle q hq hq0 hirr π₀ hπ₀ hc)

end KellyReversibility.Reversibility

end
-- END MODULE ProcessKolmogorov

-- BEGIN MODULE PublicSolution
section

open KellyReversibility.Reversibility

/-- Theorem 1.8 (Kelly, p. 23). -/
theorem solution {S : Type*} [Fintype S] [DecidableEq S]
    (q : S → S → ℝ) (hq : ∀ j k, j ≠ k → 0 ≤ q j k) (hq0 : ∀ j, q j j = 0)
    (hirr : RatesIrreducible q)
    (π₀ : S → ℝ) (hπ₀ : IsEquilibrium π₀ q) :
    ProcessReversible q π₀ ↔ KolmogorovCycle q := by
  exact KellyReversibility.Reversibility.process_kolmogorov_criterion q hq hq0 hirr π₀ hπ₀



end
-- END MODULE PublicSolution

#print axioms KellyReversibility.Reversibility.process_kolmogorov_criterion
#print axioms solution
