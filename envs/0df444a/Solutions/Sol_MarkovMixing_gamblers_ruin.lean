-- Prove2me | solution 1 for MarkovMixing.gamblers_ruin
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-22T22:58:31.02258+00:00
-- url     : https://prove2.me/submissions/4bb88b90-fc34-4612-add9-b589b88a222b

import Definitions.Def_mm_classical
import Mathlib.Algebra.BigOperators.Fin

/-!
# Gambler's ruin (LPW Proposition 2.1)
-/

namespace MarkovMixing

noncomputable section
open scoped BigOperators
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Split a trajectory into its first state and the remaining trajectory. -/
private def consEquiv (V : Type*) (t : ℕ) :
    (V × (Fin (t + 1) → V)) ≃ (Fin (t + 2) → V) where
  toFun p := Fin.cons p.1 p.2
  invFun ω := (ω 0, fun j => ω j.succ)
  left_inv := by intro p; ext <;> simp
  right_inv := by
    intro ω
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j; simp

private lemma cons_sum {t : ℕ} (F : (Fin (t + 2) → V) → ℝ) :
    ∑ ω : Fin (t + 2) → V, F ω
      = ∑ v : V, ∑ ω' : Fin (t + 1) → V, F (Fin.cons v ω') := by
  rw [← Equiv.sum_comp (consEquiv V t) F, Fintype.sum_prod_type]
  rfl

private lemma pathWeight_cons (P : Matrix V V ℝ) {t : ℕ} (v : V)
    (ω' : Fin (t + 1) → V) :
    pathWeight P (Fin.cons v ω' : Fin (t + 2) → V)
      = P v (ω' 0) * pathWeight P ω' := by
  simp only [pathWeight]
  rw [Fin.prod_univ_succ]
  have h0 : ((Fin.cons v ω' : Fin (t + 2) → V) (0 : Fin (t + 1)).castSucc) = v := by
    simp
  have h1 : ((Fin.cons v ω' : Fin (t + 2) → V) (0 : Fin (t + 1)).succ) = ω' 0 := by
    simp
  rw [h0, h1]
  congr 1

private lemma group_by_head {t : ℕ} (F : (Fin (t + 1) → V) → ℝ) :
    ∑ ω : Fin (t + 1) → V, F ω
      = ∑ y : V, ∑ ω : Fin (t + 1) → V, (if ω 0 = y then F ω else 0) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.sum_eq_single (ω 0)]
  · rw [if_pos rfl]
  · intro b _ hb; rw [if_neg (Ne.symm hb)]
  · intro hc; exact absurd (Finset.mem_univ _) hc

private lemma avoidTail_zero (P : Matrix V V ℝ) (x : V) (S : Finset V) :
    setAvoidTailProb P x S 0 = if x ∈ S then 0 else 1 := by
  classical
  simp only [setAvoidTailProb]
  rw [Finset.sum_eq_single (fun _ => x)]
  · have hall : (∀ i : Fin 1, (fun _ => x) i ∉ S) ↔ x ∉ S := by
      constructor
      · intro h; exact h 0
      · intro h i; exact h
    by_cases hx : x ∈ S
    · rw [if_neg (by simp [hall, hx]), if_pos hx]
    · rw [if_pos ⟨rfl, by simpa [hall] using hx⟩, if_neg hx]
      simp [pathWeight]
  · intro b _ hb
    have hb0 : b 0 ≠ x := by
      intro h
      refine hb (funext fun i => ?_)
      have hi : i = (0 : Fin (0 + 1)) := Fin.ext (by omega)
      rw [hi]; exact h
    rw [if_neg (fun hc => hb0 hc.1)]
  · intro hc; exact absurd (Finset.mem_univ _) hc

private lemma avoidTail_succ (P : Matrix V V ℝ) (x : V) (S : Finset V) (t : ℕ) :
    setAvoidTailProb P x S (t + 1)
      = if x ∈ S then 0 else ∑ y, P x y * setAvoidTailProb P y S t := by
  classical
  simp only [setAvoidTailProb]
  rw [cons_sum]
  have hcons : ∀ (v : V) (ω' : Fin (t + 1) → V),
      (if (Fin.cons v ω' : Fin (t + 2) → V) 0 = x ∧
          (∀ i : Fin (t + 2), (Fin.cons v ω' : Fin (t + 2) → V) i ∉ S)
        then pathWeight P (Fin.cons v ω' : Fin (t + 2) → V) else 0)
      = (if v = x ∧ (v ∉ S ∧ ∀ j : Fin (t + 1), ω' j ∉ S)
          then P v (ω' 0) * pathWeight P ω' else 0) := by
    intro v ω'
    rw [pathWeight_cons]
    refine if_congr ?_ rfl rfl
    · simp only [Fin.cons_zero]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h2 0, fun j => by have := h2 j.succ; rwa [Fin.cons_succ] at this⟩
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, fun i => ?_⟩
        refine Fin.cases ?_ ?_ i
        · simpa using h2
        · intro j; rw [Fin.cons_succ]; exact h3 j
  rw [Finset.sum_congr rfl fun v _ =>
    Finset.sum_congr rfl fun ω' _ => hcons v ω']
  rw [Finset.sum_eq_single x]
  · by_cases hx : x ∈ S
    · rw [if_pos hx]
      refine Finset.sum_eq_zero fun ω' _ => ?_
      rw [if_neg (fun hc => hc.2.1 hx)]
    · rw [if_neg hx]
      have hstep : ∀ ω' : Fin (t + 1) → V,
          (if x = x ∧ (x ∉ S ∧ ∀ j : Fin (t + 1), ω' j ∉ S)
            then P x (ω' 0) * pathWeight P ω' else 0)
          = (if (∀ j : Fin (t + 1), ω' j ∉ S)
              then P x (ω' 0) * pathWeight P ω' else 0) := by
        intro ω'
        by_cases hc : ∀ j : Fin (t + 1), ω' j ∉ S
        · rw [if_pos ⟨rfl, hx, hc⟩, if_pos hc]
        · rw [if_neg (fun h => hc h.2.2), if_neg hc]
      rw [Finset.sum_congr rfl fun ω' _ => hstep ω',
        group_by_head (fun ω' : Fin (t + 1) → V =>
          if (∀ j : Fin (t + 1), ω' j ∉ S)
            then P x (ω' 0) * pathWeight P ω' else 0)]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω' _ => ?_
      by_cases hy : ω' 0 = y
      · by_cases hc : ∀ j : Fin (t + 1), ω' j ∉ S
        · rw [if_pos hy, if_pos hc, if_pos ⟨hy, hc⟩, hy]
        · rw [if_pos hy, if_neg hc, if_neg (fun h => hc h.2), mul_zero]
      · rw [if_neg hy, if_neg (fun h => hy h.1), mul_zero]
  · intro v _ hv
    refine Finset.sum_eq_zero fun ω' _ => ?_
    rw [if_neg (fun hc => hv hc.1)]
  · intro hc; exact absurd (Finset.mem_univ _) hc

private lemma firstHit_zero (P : Matrix V V ℝ) (x a b : V) :
    firstHitBeforeProb P x a b 0 = if x = a ∧ x ≠ b then 1 else 0 := by
  classical
  simp only [firstHitBeforeProb]
  rw [Finset.sum_eq_single (fun _ => x)]
  · have hone : ∀ i : Fin (0 + 1), i = (0 : Fin (0 + 1)) := fun i => Fin.ext (by omega)
    by_cases hc : x = a ∧ x ≠ b
    · rw [if_pos, if_pos hc]
      · simp [pathWeight]
      · refine ⟨rfl, hc.1, fun i hi => absurd (hone i) ?_, fun i => hc.2⟩
        intro h
        exact hi (by rw [h]; rfl)
    · rw [if_neg hc, if_neg]
      intro hcon
      exact hc ⟨hcon.2.1, fun h => hcon.2.2.2 0 h⟩
  · intro c _ hc
    have hc0 : c 0 ≠ x := by
      intro h
      refine hc (funext fun i => ?_)
      have hi : i = (0 : Fin (0 + 1)) := Fin.ext (by omega)
      rw [hi]; exact h
    rw [if_neg (fun hh => hc0 hh.1)]
  · intro hc; exact absurd (Finset.mem_univ _) hc

private lemma firstHit_succ (P : Matrix V V ℝ) (x a b : V) (t : ℕ) :
    firstHitBeforeProb P x a b (t + 1)
      = if x ≠ a ∧ x ≠ b then ∑ y, P x y * firstHitBeforeProb P y a b t
        else 0 := by
  classical
  simp only [firstHitBeforeProb]
  rw [cons_sum]
  have hlast : ∀ (v : V) (ω' : Fin (t + 1) → V),
      (Fin.cons v ω' : Fin (t + 2) → V) (Fin.last (t + 1)) = ω' (Fin.last t) := by
    intro v ω'
    rw [← Fin.succ_last, Fin.cons_succ]
  have hcons : ∀ (v : V) (ω' : Fin (t + 1) → V),
      (if (Fin.cons v ω' : Fin (t + 2) → V) 0 = x ∧
          (Fin.cons v ω' : Fin (t + 2) → V) (Fin.last (t + 1)) = a ∧
          (∀ i : Fin (t + 2), i ≠ Fin.last (t + 1) →
            (Fin.cons v ω' : Fin (t + 2) → V) i ≠ a) ∧
          (∀ i : Fin (t + 2), (Fin.cons v ω' : Fin (t + 2) → V) i ≠ b)
        then pathWeight P (Fin.cons v ω' : Fin (t + 2) → V) else 0)
      = (if v = x ∧ ((v ≠ a ∧ v ≠ b) ∧
            (ω' (Fin.last t) = a ∧
              (∀ j : Fin (t + 1), j ≠ Fin.last t → ω' j ≠ a) ∧
              (∀ j : Fin (t + 1), ω' j ≠ b)))
          then P v (ω' 0) * pathWeight P ω' else 0) := by
    intro v ω'
    rw [pathWeight_cons]
    refine if_congr ?_ rfl rfl
    rw [Fin.cons_zero, hlast]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨h1, ⟨?_, h4 0⟩, h2, ?_, ?_⟩
      · refine h3 0 ?_
        intro hcon
        have := congrArg Fin.val hcon
        simp at this
      · intro j hj
        have := h3 j.succ (by
          intro hcon
          rw [← Fin.succ_last] at hcon
          exact hj (Fin.succ_injective _ hcon))
        rwa [Fin.cons_succ] at this
      · intro j
        have := h4 j.succ
        rwa [Fin.cons_succ] at this
    · rintro ⟨h1, ⟨hva, hvb⟩, h2, h3, h4⟩
      refine ⟨h1, h2, ?_, ?_⟩
      · intro i
        induction i using Fin.cases with
        | zero => intro _; simpa using hva
        | succ j =>
            intro hi
            rw [Fin.cons_succ]
            refine h3 j ?_
            intro hcon
            exact hi (by rw [hcon, Fin.succ_last])
      · intro i
        refine Fin.cases ?_ ?_ i
        · simpa using hvb
        · intro j; rw [Fin.cons_succ]; exact h4 j
  rw [Finset.sum_congr rfl fun v _ =>
    Finset.sum_congr rfl fun ω' _ => hcons v ω']
  rw [Finset.sum_eq_single x]
  · by_cases hx : x ≠ a ∧ x ≠ b
    · rw [if_pos hx]
      have hstep : ∀ ω' : Fin (t + 1) → V,
          (if x = x ∧ ((x ≠ a ∧ x ≠ b) ∧
              (ω' (Fin.last t) = a ∧
                (∀ j : Fin (t + 1), j ≠ Fin.last t → ω' j ≠ a) ∧
                (∀ j : Fin (t + 1), ω' j ≠ b)))
            then P x (ω' 0) * pathWeight P ω' else 0)
          = (if (ω' (Fin.last t) = a ∧
                (∀ j : Fin (t + 1), j ≠ Fin.last t → ω' j ≠ a) ∧
                (∀ j : Fin (t + 1), ω' j ≠ b))
              then P x (ω' 0) * pathWeight P ω' else 0) := by
        intro ω'
        by_cases hc : (ω' (Fin.last t) = a ∧
            (∀ j : Fin (t + 1), j ≠ Fin.last t → ω' j ≠ a) ∧
            (∀ j : Fin (t + 1), ω' j ≠ b))
        · rw [if_pos ⟨rfl, hx, hc⟩, if_pos hc]
        · rw [if_neg (fun h => hc h.2.2), if_neg hc]
      rw [Finset.sum_congr rfl fun ω' _ => hstep ω',
        group_by_head (fun ω' : Fin (t + 1) → V =>
          if (ω' (Fin.last t) = a ∧
              (∀ j : Fin (t + 1), j ≠ Fin.last t → ω' j ≠ a) ∧
              (∀ j : Fin (t + 1), ω' j ≠ b))
            then P x (ω' 0) * pathWeight P ω' else 0)]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω' _ => ?_
      by_cases hy : ω' 0 = y
      · by_cases hc : (ω' (Fin.last t) = a ∧
            (∀ j : Fin (t + 1), j ≠ Fin.last t → ω' j ≠ a) ∧
            (∀ j : Fin (t + 1), ω' j ≠ b))
        · rw [if_pos hy, if_pos hc, if_pos ⟨hy, hc⟩, hy]
        · rw [if_pos hy, if_neg hc, if_neg (fun h => hc h.2), mul_zero]
      · rw [if_neg hy, if_neg (fun h => hy h.1), mul_zero]
    · rw [if_neg hx]
      refine Finset.sum_eq_zero fun ω' _ => ?_
      rw [if_neg (fun hc => hx hc.2.1)]
  · intro v _ hv
    refine Finset.sum_eq_zero fun ω' _ => ?_
    rw [if_neg (fun hc => hv hc.1)]
  · intro hc; exact absurd (Finset.mem_univ _) hc

private lemma gc_nonneg (n : ℕ) (k l : Fin (n + 1)) : 0 ≤ gamblersChain n k l := by
  simp only [gamblersChain]
  split_ifs <;> norm_num

private lemma absorb_step (n : ℕ) (k : Fin (n + 1)) (hk : k = 0 ∨ k = Fin.last n)
    (f : Fin (n + 1) → ℝ) : ∑ l, gamblersChain n k l * f l = f k := by
  classical
  simp only [gamblersChain, if_pos hk]
  rw [Finset.sum_eq_single k]
  · rw [if_pos rfl, one_mul]
  · intro b _ hb; rw [if_neg hb, zero_mul]
  · intro hc; exact absurd (Finset.mem_univ _) hc

private lemma interior_step (n : ℕ) (k : Fin (n + 1)) (hk1 : 1 ≤ k.val)
    (hk2 : k.val + 1 ≤ n) (f : Fin (n + 1) → ℝ) :
    ∑ l, gamblersChain n k l * f l
      = (f ⟨k.val - 1, by omega⟩ + f ⟨k.val + 1, by omega⟩) / 2 := by
  classical
  have hne : ¬(k = 0 ∨ k = Fin.last n) := by
    rintro (h | h)
    · rw [h] at hk1; simp at hk1
    · rw [h] at hk2; simp only [Fin.val_last] at hk2; omega
  simp only [gamblersChain, if_neg hne]
  have hstep : ∀ l : Fin (n + 1),
      (if l.val = k.val + 1 ∨ l.val + 1 = k.val then (1 : ℝ) / 2 else 0) * f l
        = if l.val = k.val + 1 ∨ l.val + 1 = k.val then (1 : ℝ) / 2 * f l else 0 := by
    intro l; split_ifs <;> ring
  rw [Finset.sum_congr rfl fun l _ => hstep l, ← Finset.sum_filter]
  have hfilter : (Finset.univ.filter
      fun l : Fin (n + 1) => l.val = k.val + 1 ∨ l.val + 1 = k.val)
      = {(⟨k.val - 1, by omega⟩ : Fin (n + 1)),
         (⟨k.val + 1, by omega⟩ : Fin (n + 1))} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
    omega
  rw [hfilter, Finset.sum_pair (by simp only [ne_eq, Fin.ext_iff]; omega)]
  ring

private lemma gc_stochastic (n : ℕ) : IsStochastic (gamblersChain n) := by
  refine ⟨gc_nonneg n, fun k => ?_⟩
  have h1 : ∑ l, gamblersChain n k l = ∑ l, gamblersChain n k l * (1 : ℝ) := by
    simp
  by_cases hk : k = 0 ∨ k = Fin.last n
  · rw [h1, absorb_step n k hk (fun _ => (1 : ℝ))]
  · push_neg at hk
    have hk1 : 1 ≤ k.val := by
      rcases Nat.eq_zero_or_pos k.val with h | h
      · exact absurd (Fin.ext h) hk.1
      · exact h
    have hk2 : k.val + 1 ≤ n := by
      have : k.val ≠ n := by
        intro h; exact hk.2 (Fin.ext (by simp [Fin.val_last, h]))
      have := k.isLt
      omega
    rw [h1, interior_step n k hk1 hk2 (fun _ => (1 : ℝ))]
    norm_num

private lemma gc_pow_nonneg (n : ℕ) (m : ℕ) (k l : Fin (n + 1)) :
    0 ≤ ((gamblersChain n) ^ m) k l := by
  induction m generalizing k with
  | zero =>
      simp only [pow_zero, Matrix.one_apply]
      split_ifs <;> norm_num
  | succ p ih =>
      rw [pow_succ', Matrix.mul_apply]
      exact Finset.sum_nonneg fun w _ => mul_nonneg (gc_nonneg n k w) (ih w)

private lemma absorb_pow (n : ℕ) (m : ℕ) (k : Fin (n + 1))
    (hk : k = 0 ∨ k = Fin.last n) : ((gamblersChain n) ^ m) k k = 1 := by
  induction m with
  | zero => simp [Matrix.one_apply]
  | succ p ih =>
      have : ((gamblersChain n) ^ (p + 1)) k k
          = ∑ w, gamblersChain n k w * ((gamblersChain n) ^ p) w k := by
        rw [pow_succ']; exact Matrix.mul_apply
      rw [this, absorb_step n k hk (fun w => ((gamblersChain n) ^ p) w k), ih]

private lemma descent (n : ℕ) (hn : 0 < n) :
    ∀ (m : ℕ) (k : Fin (n + 1)), k.val ≤ m → k.val < n →
      (1 / 2 : ℝ) ^ m ≤ ((gamblersChain n) ^ m) k 0 := by
  intro m
  induction m with
  | zero =>
      intro k hk _
      have hkv : k.val = 0 := by omega
      have hk0 : k = 0 := Fin.ext (by simpa using hkv)
      subst hk0
      simp [Matrix.one_apply]
  | succ p ih =>
      intro k hk hkn
      have hexp : ((gamblersChain n) ^ (p + 1)) k 0
          = ∑ w, gamblersChain n k w * ((gamblersChain n) ^ p) w 0 := by
        rw [pow_succ']; exact Matrix.mul_apply
      by_cases hk0 : k = 0
      · subst hk0
        rw [hexp, absorb_step n 0 (Or.inl rfl)
          (fun w => ((gamblersChain n) ^ p) w 0)]
        have := ih 0 (by simp) hn
        calc (1 / 2 : ℝ) ^ (p + 1) ≤ (1 / 2 : ℝ) ^ p := by
              apply pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
          _ ≤ ((gamblersChain n) ^ p) 0 0 := this
      · have hk1 : 1 ≤ k.val := by
          rcases Nat.eq_zero_or_pos k.val with h | h
          · exact absurd (Fin.ext h) hk0
          · exact h
        have hk2 : k.val + 1 ≤ n := by omega
        rw [hexp, interior_step n k hk1 hk2
          (fun w => ((gamblersChain n) ^ p) w 0)]
        have hm := ih (⟨k.val - 1, by omega⟩ : Fin (n + 1))
          (by show k.val - 1 ≤ p; omega) (by show k.val - 1 < n; omega)
        have hp := gc_pow_nonneg n p (⟨k.val + 1, by omega⟩ : Fin (n + 1)) 0
        have : (1 / 2 : ℝ) ^ (p + 1) = (1 / 2 : ℝ) ^ p / 2 := by ring
        rw [this]
        linarith

private lemma escape (n : ℕ) (hn : 0 < n) (k : Fin (n + 1)) :
    (1 / 2 : ℝ) ^ n
      ≤ ((gamblersChain n) ^ n) k 0 + ((gamblersChain n) ^ n) k (Fin.last n) := by
  by_cases hk : k = Fin.last n
  · subst hk
    have h1 := absorb_pow n n (Fin.last n) (Or.inr rfl)
    have h2 := gc_pow_nonneg n n (Fin.last n) 0
    have h3 : (1 / 2 : ℝ) ^ n ≤ 1 := by
      apply pow_le_one₀ <;> norm_num
    linarith
  · have hkn : k.val < n := by
      have := k.isLt
      have : k.val ≠ n := fun h => hk (Fin.ext (by simp [Fin.val_last, h]))
      omega
    have h1 := descent n hn n k (by omega) hkn
    have h2 := gc_pow_nonneg n n k (Fin.last n)
    linarith

private lemma iter_rec (n : ℕ) (e : ℕ → Fin (n + 1) → ℝ)
    (hrec : ∀ T x, e (T + 1) x = ∑ y, gamblersChain n x y * e T y) :
    ∀ (m T : ℕ) (x : Fin (n + 1)),
      e (T + m) x = ∑ y, ((gamblersChain n) ^ m) x y * e T y := by
  intro m
  induction m with
  | zero =>
      intro T x
      simp only [Nat.add_zero, pow_zero, Matrix.one_apply]
      rw [Finset.sum_eq_single x]
      · rw [if_pos rfl, one_mul]
      · intro b _ hb; rw [if_neg (Ne.symm hb), zero_mul]
      · intro hc; exact absurd (Finset.mem_univ _) hc
  | succ p ih =>
      intro T x
      have h1 : T + (p + 1) = (T + p) + 1 := by ring
      rw [h1, hrec (T + p) x]
      have h2 : ∀ y, gamblersChain n x y * e (T + p) y
          = ∑ z, gamblersChain n x y * (((gamblersChain n) ^ p) y z * e T z) := by
        intro y
        rw [ih T y, Finset.mul_sum]
      rw [Finset.sum_congr rfl fun y _ => h2 y, Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => ?_
      have h3 : ((gamblersChain n) ^ (p + 1)) x z
          = ∑ y, gamblersChain n x y * ((gamblersChain n) ^ p) y z := by
        rw [pow_succ']; exact Matrix.mul_apply
      rw [h3, Finset.sum_mul]
      exact Finset.sum_congr rfl fun y _ => by ring

private lemma decay (n : ℕ) (hn : 0 < n) (e : ℕ → Fin (n + 1) → ℝ)
    (hrec : ∀ T x, e (T + 1) x = ∑ y, gamblersChain n x y * e T y)
    (hz0 : ∀ T, e T 0 = 0) (hzl : ∀ T, e T (Fin.last n) = 0) (x : Fin (n + 1)) :
    Filter.Tendsto (fun T => e T x) Filter.atTop (nhds 0) := by
  classical
  have hne : (Finset.univ : Finset (Fin (n + 1))).Nonempty := ⟨0, Finset.mem_univ 0⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ → ℝ,
      M = fun T => Finset.univ.sup' hne (fun z => |e T z|) := ⟨_, rfl⟩
  have hMle : ∀ T z, |e T z| ≤ M T := by
    intro T z
    rw [hMdef]
    exact Finset.le_sup' (fun z => |e T z|) (Finset.mem_univ z)
  have hM0 : ∀ T, 0 ≤ M T := fun T => le_trans (abs_nonneg _) (hMle T 0)
  have hMsup : ∀ (T : ℕ) (a : ℝ), (∀ z, |e T z| ≤ a) → M T ≤ a := by
    intro T a ha
    rw [hMdef]
    exact Finset.sup'_le hne _ fun z _ => ha z
  have hstoch := gc_stochastic n
  have hMstep : ∀ T, M (T + 1) ≤ M T := by
    intro T
    refine hMsup (T + 1) (M T) fun z => ?_
    rw [hrec T z]
    calc |∑ y, gamblersChain n z y * e T y|
        ≤ ∑ y, |gamblersChain n z y * e T y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, gamblersChain n z y * M T := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [abs_mul, abs_of_nonneg (gc_nonneg n z y)]
          exact mul_le_mul_of_nonneg_left (hMle T y) (gc_nonneg n z y)
      _ = M T := by rw [← Finset.sum_mul, hstoch.2 z, one_mul]
  have hMmono : ∀ T T', T ≤ T' → M T' ≤ M T := by
    intro T T' h
    induction T' with
    | zero => rw [Nat.le_zero] at h; rw [h]
    | succ p ih =>
        rcases Nat.lt_or_ge T (p + 1) with hlt | hge
        · exact le_trans (hMstep p) (ih (by omega))
        · have : T = p + 1 := by omega
          rw [this]
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 1 - (1 / 2 : ℝ) ^ n := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by
    rw [hcdef]
    have : (1 / 2 : ℝ) ^ n ≤ 1 := by apply pow_le_one₀ <;> norm_num
    linarith
  have hc1 : c < 1 := by
    rw [hcdef]
    have : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
    linarith
  have hpair : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have := congrArg Fin.val h
    simp [Fin.val_last] at this
    omega
  have hMcontr : ∀ T, M (T + n) ≤ c * M T := by
    intro T
    refine hMsup (T + n) (c * M T) fun z => ?_
    rw [iter_rec n e hrec n T z]
    have hsplit : ∑ y, |((gamblersChain n) ^ n) z y * e T y|
        = ∑ y ∈ (Finset.univ \ {(0 : Fin (n + 1)), Fin.last n}),
            |((gamblersChain n) ^ n) z y * e T y| := by
      rw [← Finset.sum_sdiff (Finset.subset_univ
        ({(0 : Fin (n + 1)), Fin.last n} : Finset (Fin (n + 1))))]
      rw [Finset.sum_pair hpair, hz0 T, hzl T]
      simp
    have hsub : ∑ y ∈ (Finset.univ \ {(0 : Fin (n + 1)), Fin.last n}),
        ((gamblersChain n) ^ n) z y
        = 1 - (((gamblersChain n) ^ n) z 0 + ((gamblersChain n) ^ n) z (Fin.last n)) := by
      have hall : ∑ y, ((gamblersChain n) ^ n) z y = 1 := by
        have := iter_rec n (fun _ w => (1 : ℝ)) (fun T w => by
          rw [← Finset.sum_mul, hstoch.2 w, one_mul]) n 0 z
        simpa using this.symm
      have := Finset.sum_sdiff (f := fun y => ((gamblersChain n) ^ n) z y)
        (Finset.subset_univ ({(0 : Fin (n + 1)), Fin.last n} : Finset (Fin (n + 1))))
      rw [Finset.sum_pair hpair] at this
      rw [hall] at this
      linarith
    calc |∑ y, ((gamblersChain n) ^ n) z y * e T y|
        ≤ ∑ y, |((gamblersChain n) ^ n) z y * e T y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ y ∈ (Finset.univ \ {(0 : Fin (n + 1)), Fin.last n}),
            |((gamblersChain n) ^ n) z y * e T y| := hsplit
      _ ≤ ∑ y ∈ (Finset.univ \ {(0 : Fin (n + 1)), Fin.last n}),
            ((gamblersChain n) ^ n) z y * M T := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [abs_mul, abs_of_nonneg (gc_pow_nonneg n n z y)]
          exact mul_le_mul_of_nonneg_left (hMle T y) (gc_pow_nonneg n n z y)
      _ = (1 - (((gamblersChain n) ^ n) z 0
            + ((gamblersChain n) ^ n) z (Fin.last n))) * M T := by
          rw [← Finset.sum_mul, hsub]
      _ ≤ c * M T := by
          have hesc := escape n hn z
          have := hM0 T
          rw [hcdef]
          nlinarith [hM0 T]
  have hMpow : ∀ j : ℕ, M (j * n) ≤ c ^ j * M 0 := by
    intro j
    induction j with
    | zero => simp
    | succ i ih =>
        have h1 : (i + 1) * n = i * n + n := by ring
        rw [h1]
        calc M (i * n + n) ≤ c * M (i * n) := hMcontr (i * n)
          _ ≤ c * (c ^ i * M 0) := mul_le_mul_of_nonneg_left ih hc0
          _ = c ^ (i + 1) * M 0 := by ring
  have hMfinal : ∀ T, M T ≤ c ^ (T / n) * M 0 := by
    intro T
    calc M T ≤ M ((T / n) * n) := hMmono _ _ (Nat.div_mul_le_self T n)
      _ ≤ c ^ (T / n) * M 0 := hMpow _
  have hlim : Filter.Tendsto (fun T : ℕ => c ^ (T / n) * M 0) Filter.atTop (nhds 0) := by
    have hdiv : Filter.Tendsto (fun T : ℕ => T / n) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop_atTop.mpr fun b => ⟨b * n + n, fun a ha => ?_⟩
      have : b * n + n ≤ a := ha
      have hb : b < a / n := by
        rw [Nat.lt_div_iff_mul_lt hn]
        omega
      omega
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).comp hdiv
    have h2 := this.mul_const (M 0)
    simpa using h2
  have hlo : Filter.Tendsto (fun T : ℕ => -(c ^ (T / n) * M 0)) Filter.atTop (nhds 0) := by
    simpa using hlim.neg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hlim (fun T => ?_) (fun T => ?_)
  · have := le_trans (hMle T x) (hMfinal T)
    have h2 := neg_le_of_abs_le (le_trans (hMle T x) (hMfinal T))
    exact h2
  · exact le_of_abs_le (le_trans (hMle T x) (hMfinal T))

private lemma tsum_of_partial (v : ℕ → ℝ) (L : ℝ) (hnn : ∀ t, 0 ≤ v t)
    (hlim : Filter.Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), v t)
      Filter.atTop (nhds L)) : (∑' t, v t) = L := by
  have hlim' : Filter.Tendsto (fun m => ∑ t ∈ Finset.range m, v t)
      Filter.atTop (nhds L) := (Filter.tendsto_add_atTop_iff_nat 1).mp hlim
  have hmono : Monotone fun m => ∑ t ∈ Finset.range m, v t := by
    intro a b hab
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (fun i hi => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hi) hab)) fun i _ _ => hnn i
  have hle : ∀ m, ∑ t ∈ Finset.range m, v t ≤ L := hmono.ge_of_tendsto hlim'
  have hsum : Summable v := summable_of_sum_range_le hnn hle
  exact tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlim'

private lemma pathWeight_nonneg (n : ℕ) {t : ℕ} (ω : Fin (t + 1) → Fin (n + 1)) :
    0 ≤ pathWeight (gamblersChain n) ω :=
  Finset.prod_nonneg fun i _ => gc_nonneg n _ _

private lemma avoidTail_nonneg (n : ℕ) (x : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (t : ℕ) : 0 ≤ setAvoidTailProb (gamblersChain n) x S t := by
  refine Finset.sum_nonneg fun ω _ => ?_
  split_ifs
  · exact pathWeight_nonneg n ω
  · exact le_rfl

private lemma firstHit_nonneg (n : ℕ) (x a b : Fin (n + 1)) (t : ℕ) :
    0 ≤ firstHitBeforeProb (gamblersChain n) x a b t := by
  refine Finset.sum_nonneg fun ω _ => ?_
  split_ifs
  · exact pathWeight_nonneg n ω
  · exact le_rfl

end

end MarkovMixing

open MarkovMixing

/-- **Proposition 2.1** (LPW), gambler's ruin. -/
theorem solution (n : ℕ) (hn : 0 < n) (k : Fin (n + 1)) :
    hitBeforeProb (gamblersChain n) k (Fin.last n) 0 = (k.val : ℝ) / n ∧
    expSetHitTime (gamblersChain n) k {0, Fin.last n} =
      (k.val : ℝ) * ((n : ℝ) - (k.val : ℝ)) := by
  classical
  have hlast0 : (Fin.last n) ≠ (0 : Fin (n + 1)) := by
    intro h
    have := congrArg Fin.val h
    simp [Fin.val_last] at this
    omega
  -- interior characterisation
  have hint : ∀ x : Fin (n + 1), x ≠ 0 → x ≠ Fin.last n → 1 ≤ x.val ∧ x.val + 1 ≤ n := by
    intro x h0 hl
    constructor
    · rcases Nat.eq_zero_or_pos x.val with h | h
      · exact absurd (Fin.ext (by simpa using h)) h0
      · exact h
    · have hxv : x.val ≠ n := by
        intro h
        exact hl (Fin.ext (by simp [Fin.val_last, h]))
      have := x.isLt
      omega
  ------------------------------------------------------------------
  -- Part 2: the expected absorption time
  ------------------------------------------------------------------
  have hSmem : ∀ x : Fin (n + 1),
      x ∈ ({0, Fin.last n} : Finset (Fin (n + 1))) ↔ (x = 0 ∨ x = Fin.last n) := by
    intro x; simp
  obtain ⟨g, hgdef⟩ : ∃ g : Fin (n + 1) → ℝ,
      g = fun x => (x.val : ℝ) * ((n : ℝ) - (x.val : ℝ)) := ⟨_, rfl⟩
  obtain ⟨u, hudef⟩ : ∃ u : ℕ → Fin (n + 1) → ℝ,
      u = fun T x => setAvoidTailProb (gamblersChain n) x
        ({0, Fin.last n} : Finset (Fin (n + 1))) T := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E : ℕ → Fin (n + 1) → ℝ,
      E = fun T x => g x - ∑ t ∈ Finset.range (T + 1), u t x := ⟨_, rfl⟩
  have hg_int : ∀ x : Fin (n + 1), x ≠ 0 → x ≠ Fin.last n →
      ∑ y, gamblersChain n x y * g y = g x - 1 := by
    intro x h0 hl
    obtain ⟨h1, h2⟩ := hint x h0 hl
    rw [interior_step n x h1 h2 g, hgdef]
    have hc1 : ((x.val - 1 : ℕ) : ℝ) = (x.val : ℝ) - 1 := by
      rw [Nat.cast_sub h1]; norm_num
    simp only []
    rw [hc1]
    push_cast
    ring
  have hu0 : ∀ x, u 0 x = if x = 0 ∨ x = Fin.last n then 0 else 1 := by
    intro x
    rw [hudef]
    simp only []
    rw [avoidTail_zero]
    by_cases h : x = 0 ∨ x = Fin.last n
    · rw [if_pos ((hSmem x).mpr h), if_pos h]
    · rw [if_neg (fun hc => h ((hSmem x).mp hc)), if_neg h]
  have husucc : ∀ T x, u (T + 1) x
      = if x = 0 ∨ x = Fin.last n then 0 else ∑ y, gamblersChain n x y * u T y := by
    intro T x
    rw [hudef]
    simp only []
    rw [avoidTail_succ]
    by_cases h : x = 0 ∨ x = Fin.last n
    · rw [if_pos ((hSmem x).mpr h), if_pos h]
    · rw [if_neg (fun hc => h ((hSmem x).mp hc)), if_neg h]
  have huabs : ∀ T x, (x = 0 ∨ x = Fin.last n) → u T x = 0 := by
    intro T x hx
    cases T with
    | zero => rw [hu0, if_pos hx]
    | succ p => rw [husucc, if_pos hx]
  have hEabs : ∀ T x, (x = 0 ∨ x = Fin.last n) → E T x = 0 := by
    intro T x hx
    rw [hEdef]
    simp only []
    have hgx : g x = 0 := by
      rw [hgdef]
      rcases hx with h | h <;> subst h <;> simp [Fin.val_last]
    rw [hgx, Finset.sum_eq_zero fun t _ => huabs t x hx]
    ring
  have hErec : ∀ T x, E (T + 1) x = ∑ y, gamblersChain n x y * E T y := by
    intro T x
    by_cases hx : x = 0 ∨ x = Fin.last n
    · rw [hEabs (T + 1) x hx, absorb_step n x hx (fun y => E T y), hEabs T x hx]
    · push_neg at hx
      have hsplit : ∑ t ∈ Finset.range (T + 1 + 1), u t x
          = 1 + ∑ y, gamblersChain n x y * ∑ t ∈ Finset.range (T + 1), u t y := by
        rw [Finset.sum_range_succ' (fun t => u t x) (T + 1), hu0 x,
          if_neg (fun h => by rcases h with h | h; exacts [hx.1 h, hx.2 h])]
        have hterm : ∀ t, u (t + 1) x = ∑ y, gamblersChain n x y * u t y := by
          intro t
          rw [husucc, if_neg (fun h => by rcases h with h | h; exacts [hx.1 h, hx.2 h])]
        rw [Finset.sum_congr rfl fun t _ => hterm t, Finset.sum_comm]
        have : ∀ y, ∑ t ∈ Finset.range (T + 1), gamblersChain n x y * u t y
            = gamblersChain n x y * ∑ t ∈ Finset.range (T + 1), u t y := by
          intro y; rw [Finset.mul_sum]
        rw [Finset.sum_congr rfl fun y _ => this y]
        ring
      rw [hEdef]
      simp only []
      rw [hsplit]
      have hgint := hg_int x hx.1 hx.2
      have hsub : ∑ y, gamblersChain n x y * (g y - ∑ t ∈ Finset.range (T + 1), u t y)
          = (∑ y, gamblersChain n x y * g y)
            - ∑ y, gamblersChain n x y * ∑ t ∈ Finset.range (T + 1), u t y := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun y _ => by ring
      rw [hsub, hgint]
      ring
  have hElim : ∀ x, Filter.Tendsto (fun T => E T x) Filter.atTop (nhds 0) :=
    decay n hn E hErec (fun T => hEabs T 0 (Or.inl rfl))
      (fun T => hEabs T (Fin.last n) (Or.inr rfl))
  have hpart2 : expSetHitTime (gamblersChain n) k
      ({0, Fin.last n} : Finset (Fin (n + 1))) = g k := by
    have hlim : Filter.Tendsto
        (fun T => ∑ t ∈ Finset.range (T + 1),
          setAvoidTailProb (gamblersChain n) k
            ({0, Fin.last n} : Finset (Fin (n + 1))) t)
        Filter.atTop (nhds (g k)) := by
      have hEq : ∀ T, ∑ t ∈ Finset.range (T + 1),
          setAvoidTailProb (gamblersChain n) k
            ({0, Fin.last n} : Finset (Fin (n + 1))) t = g k - E T k := by
        intro T
        rw [hEdef]
        simp only [hudef]
        ring
      have := (tendsto_const_nhds (x := g k) (f := Filter.atTop (α := ℕ))).sub (hElim k)
      rw [sub_zero] at this
      exact this.congr fun T => (hEq T).symm
    exact tsum_of_partial _ _
      (fun t => avoidTail_nonneg n k _ t) hlim
  ------------------------------------------------------------------
  -- Part 1: the ruin probability
  ------------------------------------------------------------------
  obtain ⟨phi, hphidef⟩ : ∃ phi : Fin (n + 1) → ℝ,
      phi = fun x => (x.val : ℝ) / (n : ℝ) := ⟨_, rfl⟩
  obtain ⟨f, hfdef⟩ : ∃ f : ℕ → Fin (n + 1) → ℝ,
      f = fun t x => firstHitBeforeProb (gamblersChain n) x (Fin.last n) 0 t := ⟨_, rfl⟩
  obtain ⟨H, hHdef⟩ : ∃ H : ℕ → Fin (n + 1) → ℝ,
      H = fun T x => ∑ t ∈ Finset.range (T + 1), f t x := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ → Fin (n + 1) → ℝ,
      D = fun T x => phi x - H T x := ⟨_, rfl⟩
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hphi_int : ∀ x : Fin (n + 1), x ≠ 0 → x ≠ Fin.last n →
      ∑ y, gamblersChain n x y * phi y = phi x := by
    intro x h0 hl
    obtain ⟨h1, h2⟩ := hint x h0 hl
    rw [interior_step n x h1 h2 phi, hphidef]
    have hc1 : ((x.val - 1 : ℕ) : ℝ) = (x.val : ℝ) - 1 := by
      rw [Nat.cast_sub h1]; norm_num
    simp only []
    rw [hc1]
    push_cast
    field_simp
    ring
  have hf0 : ∀ x, f 0 x = if x = Fin.last n then 1 else 0 := by
    intro x
    rw [hfdef]
    simp only []
    rw [firstHit_zero]
    by_cases h : x = Fin.last n
    · rw [if_pos ⟨h, by rw [h]; exact hlast0⟩, if_pos h]
    · rw [if_neg (fun hc => h hc.1), if_neg h]
  have hfsucc : ∀ t x, f (t + 1) x
      = if x ≠ Fin.last n ∧ x ≠ 0 then ∑ y, gamblersChain n x y * f t y else 0 := by
    intro t x
    rw [hfdef]
    simp only []
    rw [firstHit_succ]
  have hHabs : ∀ T, H T 0 = 0 ∧ H T (Fin.last n) = 1 := by
    intro T
    constructor
    · simp only [hHdef]
      refine Finset.sum_eq_zero fun t _ => ?_
      cases t with
      | zero => rw [hf0, if_neg (Ne.symm hlast0)]
      | succ p => rw [hfsucc, if_neg (fun hc => hc.2 rfl)]
    · simp only [hHdef]
      rw [Finset.sum_range_succ' (fun t => f t (Fin.last n)) T, hf0, if_pos rfl]
      have : ∀ p, f (p + 1) (Fin.last n) = 0 := by
        intro p; rw [hfsucc, if_neg (fun hc => hc.1 rfl)]
      rw [Finset.sum_congr rfl fun p _ => this p]
      simp
  have hDabs : ∀ T x, (x = 0 ∨ x = Fin.last n) → D T x = 0 := by
    intro T x hx
    simp only [hDdef]
    rcases hx with h | h <;> subst h
    · rw [(hHabs T).1]
      simp [hphidef]
    · rw [(hHabs T).2]
      simp only [hphidef, Fin.val_last]
      field_simp
      norm_num
  have hDrec : ∀ T x, D (T + 1) x = ∑ y, gamblersChain n x y * D T y := by
    intro T x
    by_cases hx : x = 0 ∨ x = Fin.last n
    · rw [hDabs (T + 1) x hx, absorb_step n x hx (fun y => D T y), hDabs T x hx]
    · push_neg at hx
      have hH : H (T + 1) x = ∑ y, gamblersChain n x y * H T y := by
        rw [hHdef]
        simp only []
        rw [Finset.sum_range_succ' (fun t => f t x) (T + 1), hf0, if_neg hx.2]
        have hterm : ∀ t, f (t + 1) x = ∑ y, gamblersChain n x y * f t y := by
          intro t; rw [hfsucc, if_pos ⟨hx.2, hx.1⟩]
        rw [Finset.sum_congr rfl fun t _ => hterm t, Finset.sum_comm]
        have hy : ∀ y, ∑ t ∈ Finset.range (T + 1), gamblersChain n x y * f t y
            = gamblersChain n x y * ∑ t ∈ Finset.range (T + 1), f t y := by
          intro y; rw [Finset.mul_sum]
        rw [Finset.sum_congr rfl fun y _ => hy y]
        simp
      rw [hDdef]
      simp only []
      rw [hH]
      have hsub : ∑ y, gamblersChain n x y * (phi y - H T y)
          = (∑ y, gamblersChain n x y * phi y) - ∑ y, gamblersChain n x y * H T y := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun y _ => by ring
      rw [hsub, hphi_int x hx.1 hx.2]
  have hDlim : ∀ x, Filter.Tendsto (fun T => D T x) Filter.atTop (nhds 0) :=
    decay n hn D hDrec (fun T => hDabs T 0 (Or.inl rfl))
      (fun T => hDabs T (Fin.last n) (Or.inr rfl))
  have hpart1 : hitBeforeProb (gamblersChain n) k (Fin.last n) 0 = phi k := by
    have hlim : Filter.Tendsto
        (fun T => ∑ t ∈ Finset.range (T + 1),
          firstHitBeforeProb (gamblersChain n) k (Fin.last n) 0 t)
        Filter.atTop (nhds (phi k)) := by
      have hEq : ∀ T, ∑ t ∈ Finset.range (T + 1),
          firstHitBeforeProb (gamblersChain n) k (Fin.last n) 0 t
          = phi k - D T k := by
        intro T
        rw [hDdef, hHdef]
        simp only [hfdef]
        ring
      have := (tendsto_const_nhds (x := phi k) (f := Filter.atTop (α := ℕ))).sub (hDlim k)
      rw [sub_zero] at this
      exact this.congr fun T => (hEq T).symm
    exact tsum_of_partial _ _ (fun t => firstHit_nonneg n k _ _ t) hlim
  refine ⟨?_, ?_⟩
  · rw [hpart1, hphidef]
  · rw [hpart2, hgdef]
