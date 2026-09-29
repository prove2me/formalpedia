-- Prove2me | solution 1 for MarkovEntanglement.rmab_one_step_concentration
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T00:20:32.903744+00:00
-- url     : https://prove2.me/submissions/8791aa26-001d-4d89-bcce-c18c26332141

import Mathlib
import Definitions.Def_markov_entanglement_meanfield

open scoped BigOperators
open MarkovEntanglement

namespace ME9

set_option linter.unusedSectionVars false

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ### Products supported on one or two indices -/

theorem prod_one {N : ℕ} {β : Type*} [CommMonoid β] (i : Fin N) (G : Fin N → β)
    (hG : ∀ j, j ≠ i → G j = 1) : ∏ j, G j = G i :=
  Finset.prod_eq_single i (fun b _ hb => hG b hb) (fun h => absurd (Finset.mem_univ i) h)

theorem prod_two {N : ℕ} {β : Type*} [CommMonoid β] {i k : Fin N} (hik : i ≠ k)
    (G : Fin N → β) (hG : ∀ j, j ≠ i → j ≠ k → G j = 1) : ∏ j, G j = G i * G k := by
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  congr 1
  refine Finset.prod_eq_single k (fun b hb hbk => hG b (Finset.ne_of_mem_erase hb) hbk) ?_
  intro h
  exact absurd (Finset.mem_erase.2 ⟨Ne.symm hik, Finset.mem_univ k⟩) h

/-! ### Expectations under a product measure -/

/-- Summing a product of one-coordinate functions over all joint states factorises. -/
theorem sum_prod_eq {N : ℕ} (f : Fin N → S → ℝ) :
    ∑ s' : Fin N → S, ∏ j, f j (s' j) = ∏ j, ∑ y, f j y := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- Under a product measure, the expectation of a product of one-coordinate functions is the
product of the expectations: the coordinates are independent. -/
theorem prod_expect {N : ℕ} (κ : Fin N → S → ℝ) (G : Fin N → S → ℝ) :
    ∑ s' : Fin N → S, (∏ j, κ j (s' j)) * ∏ j, G j (s' j) = ∏ j, ∑ y, κ j y * G j y := by
  rw [← sum_prod_eq (fun j y => κ j y * G j y)]
  exact Finset.sum_congr rfl fun s' _ => Finset.prod_mul_distrib.symm

theorem expect_const {N : ℕ} (κ : Fin N → S → ℝ) (hκ : ∀ j, ∑ y, κ j y = 1) :
    ∑ s' : Fin N → S, ∏ j, κ j (s' j) = 1 := by
  rw [sum_prod_eq]
  simp [hκ]

theorem expect_single {N : ℕ} (κ : Fin N → S → ℝ) (hκ : ∀ j, ∑ y, κ j y = 1)
    (i : Fin N) (g : S → ℝ) :
    ∑ s' : Fin N → S, (∏ j, κ j (s' j)) * g (s' i) = ∑ y, κ i y * g y := by
  classical
  have h1 : ∀ s' : Fin N → S, (∏ j, (if j = i then g (s' j) else (1:ℝ))) = g (s' i) := by
    intro s'
    rw [prod_one i _ (fun j hj => by simp only [if_neg hj]), if_pos rfl]
  calc ∑ s' : Fin N → S, (∏ j, κ j (s' j)) * g (s' i)
      = ∑ s' : Fin N → S, (∏ j, κ j (s' j)) * ∏ j, (if j = i then g (s' j) else (1:ℝ)) :=
        Finset.sum_congr rfl fun s' _ => by rw [h1 s']
    _ = ∏ j, ∑ y, κ j y * (if j = i then g y else (1:ℝ)) :=
        prod_expect κ (fun j y => if j = i then g y else (1:ℝ))
    _ = ∑ y, κ i y * g y := by
        rw [prod_one i _ (fun j hj => by simp only [if_neg hj, mul_one]; exact hκ j)]
        simp

theorem expect_pair {N : ℕ} (κ : Fin N → S → ℝ) (hκ : ∀ j, ∑ y, κ j y = 1)
    {i k : Fin N} (hik : i ≠ k) (g h : S → ℝ) :
    ∑ s' : Fin N → S, (∏ j, κ j (s' j)) * (g (s' i) * h (s' k))
      = (∑ y, κ i y * g y) * (∑ y, κ k y * h y) := by
  classical
  have h1 : ∀ s' : Fin N → S,
      (∏ j, (if j = i then g (s' j) else if j = k then h (s' j) else (1:ℝ)))
        = g (s' i) * h (s' k) := by
    intro s'
    rw [prod_two hik _ (fun j hj hk => by simp only [if_neg hj, if_neg hk])]
    simp [Ne.symm hik]
  calc ∑ s' : Fin N → S, (∏ j, κ j (s' j)) * (g (s' i) * h (s' k))
      = ∑ s' : Fin N → S, (∏ j, κ j (s' j))
          * ∏ j, (if j = i then g (s' j) else if j = k then h (s' j) else (1:ℝ)) :=
        Finset.sum_congr rfl fun s' _ => by rw [h1 s']
    _ = ∏ j, ∑ y, κ j y * (if j = i then g y else if j = k then h y else (1:ℝ)) :=
        prod_expect κ (fun j y => if j = i then g y else if j = k then h y else (1:ℝ))
    _ = (∑ y, κ i y * g y) * (∑ y, κ k y * h y) := by
        rw [prod_two hik _ (fun j hj hk => by
          simp only [if_neg hj, if_neg hk, mul_one]; exact hκ j)]
        simp [Ne.symm hik]

/-! ### The conditional one-step estimate -/

theorem sum_ind {N : ℕ} (s' : Fin N → S) (y : S) :
    (stateCount s' y : ℝ) = ∑ j, (if s' j = y then (1:ℝ) else 0) := by
  unfold stateCount
  rw [Finset.card_filter]
  push_cast
  rfl

theorem cond_bound {N : ℕ} (hN : 0 < N) (κ : Fin N → S → ℝ)
    (hκnn : ∀ j y, 0 ≤ κ j y) (hκ1 : ∀ j, ∑ y, κ j y = 1)
    (φ : S → ℝ) (hφ : ∀ y, ∑ j, κ j y = (N : ℝ) * φ y) :
    ∑ s' : Fin N → S, (∏ j, κ j (s' j)) *
        (∑ y, |(stateCount s' y : ℝ) / (N : ℝ) - φ y|)
      ≤ Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ)) := by
  classical
  have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hνnn : ∀ s' : Fin N → S, 0 ≤ ∏ j, κ j (s' j) :=
    fun s' => Finset.prod_nonneg fun j _ => hκnn j (s' j)
  have hνsum : ∑ s' : Fin N → S, ∏ j, κ j (s' j) = 1 := expect_const κ hκ1
  -- the centred indicators
  have hZW : ∀ (y : S) (s' : Fin N → S),
      (N:ℝ) * ((stateCount s' y : ℝ) / (N:ℝ) - φ y)
        = ∑ j, ((if s' j = y then (1:ℝ) else 0) - κ j y) := by
    intro y s'
    rw [Finset.sum_sub_distrib, ← sum_ind s' y, hφ y]
    field_simp
  -- first moments vanish
  have hE1 : ∀ (j : Fin N) (y : S),
      ∑ s' : Fin N → S, (∏ l, κ l (s' l)) * ((if s' j = y then (1:ℝ) else 0) - κ j y) = 0 := by
    intro j y
    rw [expect_single κ hκ1 j (fun z => (if z = y then (1:ℝ) else 0) - κ j y)]
    have : ∀ z : S, κ j z * ((if z = y then (1:ℝ) else 0) - κ j y)
        = (if z = y then κ j z else 0) - κ j z * κ j y := by
      intro z
      by_cases h : z = y <;> simp [h] <;> ring
    rw [Finset.sum_congr rfl (fun z _ => this z), Finset.sum_sub_distrib,
      Finset.sum_ite_eq' Finset.univ y (fun z => κ j z), ← Finset.sum_mul, hκ1 j]
    simp
  -- second moments
  have hE2diag : ∀ (j : Fin N) (y : S),
      ∑ s' : Fin N → S, (∏ l, κ l (s' l)) *
        (((if s' j = y then (1:ℝ) else 0) - κ j y) * ((if s' j = y then (1:ℝ) else 0) - κ j y))
        = κ j y - κ j y * κ j y := by
    intro j y
    rw [expect_single κ hκ1 j
      (fun z => ((if z = y then (1:ℝ) else 0) - κ j y) * ((if z = y then (1:ℝ) else 0) - κ j y))]
    have hpt : ∀ z : S, κ j z * (((if z = y then (1:ℝ) else 0) - κ j y)
        * ((if z = y then (1:ℝ) else 0) - κ j y))
        = (1 - 2 * κ j y) * (if z = y then κ j z else 0) + κ j z * (κ j y * κ j y) := by
      intro z
      by_cases h : z = y <;> simp [h] <;> ring
    rw [Finset.sum_congr rfl (fun z _ => hpt z), Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq' Finset.univ y (fun z => κ j z), ← Finset.sum_mul, hκ1 j]
    simp only [Finset.mem_univ, if_true]
    ring
  have hE2off : ∀ (j k : Fin N) (y : S), j ≠ k →
      ∑ s' : Fin N → S, (∏ l, κ l (s' l)) *
        (((if s' j = y then (1:ℝ) else 0) - κ j y) * ((if s' k = y then (1:ℝ) else 0) - κ k y))
        = 0 := by
    intro j k y hjk
    rw [expect_pair κ hκ1 hjk (fun z => (if z = y then (1:ℝ) else 0) - κ j y)
      (fun z => (if z = y then (1:ℝ) else 0) - κ k y)]
    have h1 : ∑ z, κ j z * ((if z = y then (1:ℝ) else 0) - κ j y) = 0 := by
      have := hE1 j y
      rwa [expect_single κ hκ1 j (fun z => (if z = y then (1:ℝ) else 0) - κ j y)] at this
    rw [h1, zero_mul]
  -- the second moment of the deviation
  have hkey : ∀ y : S, ∑ s' : Fin N → S, (∏ l, κ l (s' l)) *
      ((N:ℝ) * ((stateCount s' y : ℝ) / (N:ℝ) - φ y)) ^ 2
      = ∑ j, (κ j y - κ j y * κ j y) := by
    intro y
    have hexp : ∀ s' : Fin N → S,
        ((N:ℝ) * ((stateCount s' y : ℝ) / (N:ℝ) - φ y)) ^ 2
          = ∑ j, ∑ k, (((if s' j = y then (1:ℝ) else 0) - κ j y)
              * ((if s' k = y then (1:ℝ) else 0) - κ k y)) := by
      intro s'
      rw [hZW y s', sq, Finset.sum_mul_sum]
    calc ∑ s' : Fin N → S, (∏ l, κ l (s' l)) *
            ((N:ℝ) * ((stateCount s' y : ℝ) / (N:ℝ) - φ y)) ^ 2
        = ∑ s' : Fin N → S, ∑ j, ∑ k, (∏ l, κ l (s' l)) *
            (((if s' j = y then (1:ℝ) else 0) - κ j y)
              * ((if s' k = y then (1:ℝ) else 0) - κ k y)) := by
          refine Finset.sum_congr rfl fun s' _ => ?_
          rw [hexp s', Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
      _ = ∑ j, ∑ k, ∑ s' : Fin N → S, (∏ l, κ l (s' l)) *
            (((if s' j = y then (1:ℝ) else 0) - κ j y)
              * ((if s' k = y then (1:ℝ) else 0) - κ k y)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ j, (κ j y - κ j y * κ j y) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_eq_single j (fun k _ hk => hE2off j k y (Ne.symm hk))
            (fun h => absurd (Finset.mem_univ j) h)]
          exact hE2diag j y
  have hvar : ∀ y : S, ∑ s' : Fin N → S, (∏ l, κ l (s' l)) *
      ((stateCount s' y : ℝ) / (N:ℝ) - φ y) ^ 2
      = (∑ j, (κ j y - κ j y * κ j y)) / (N:ℝ) ^ 2 := by
    intro y
    rw [← hkey y, Finset.sum_div]
    refine Finset.sum_congr rfl fun s' _ => ?_
    field_simp
  have hvarle : ∑ y, ∑ s' : Fin N → S, (∏ l, κ l (s' l)) *
      ((stateCount s' y : ℝ) / (N:ℝ) - φ y) ^ 2 ≤ 1 / (N:ℝ) := by
    have hdiv : ∀ a b c : ℝ, a ≤ b → 0 < c → a / c ≤ b / c := by
      intro a b c hab hc
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hab (le_of_lt (inv_pos.2 hc))
    calc ∑ y, ∑ s' : Fin N → S, (∏ l, κ l (s' l)) *
            ((stateCount s' y : ℝ) / (N:ℝ) - φ y) ^ 2
        = ∑ y, (∑ j, (κ j y - κ j y * κ j y)) / (N:ℝ) ^ 2 :=
          Finset.sum_congr rfl fun y _ => hvar y
      _ ≤ ∑ y, (∑ j, κ j y) / (N:ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun y _ => hdiv _ _ _ ?_ (by positivity)
          refine Finset.sum_le_sum fun j _ => ?_
          nlinarith [hκnn j y]
      _ = (∑ y, ∑ j, κ j y) / (N:ℝ) ^ 2 := by rw [Finset.sum_div]
      _ = (N:ℝ) / (N:ℝ) ^ 2 := by
          rw [Finset.sum_comm]
          simp [hκ1]
      _ = 1 / (N:ℝ) := by
          field_simp
  -- Cauchy-Schwarz
  have hterm : ∀ p : S × (Fin N → S),
      Real.sqrt (∏ l, κ l (p.2 l)) *
        Real.sqrt ((∏ l, κ l (p.2 l)) * ((stateCount p.2 p.1 : ℝ) / (N:ℝ) - φ p.1) ^ 2)
      = (∏ l, κ l (p.2 l)) * |(stateCount p.2 p.1 : ℝ) / (N:ℝ) - φ p.1| := by
    intro p
    rw [Real.sqrt_mul (hνnn p.2), ← mul_assoc, Real.mul_self_sqrt (hνnn p.2),
      Real.sqrt_sq_eq_abs]
  have hCS := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (S × (Fin N → S)))
      (f := fun p : S × (Fin N → S) => ∏ l, κ l (p.2 l))
      (g := fun p : S × (Fin N → S) =>
        (∏ l, κ l (p.2 l)) * ((stateCount p.2 p.1 : ℝ) / (N:ℝ) - φ p.1) ^ 2)
      (fun p => hνnn p.2) (fun p => mul_nonneg (hνnn p.2) (sq_nonneg _))
  have hf : ∑ p : S × (Fin N → S), (∏ l, κ l (p.2 l)) = (Fintype.card S : ℝ) := by
    rw [Fintype.sum_prod_type]
    simp [hνsum]
  have hgle : ∑ p : S × (Fin N → S),
      (∏ l, κ l (p.2 l)) * ((stateCount p.2 p.1 : ℝ) / (N:ℝ) - φ p.1) ^ 2 ≤ 1 / (N:ℝ) := by
    rw [Fintype.sum_prod_type]
    exact hvarle
  have hL : ∑ p : S × (Fin N → S),
      (∏ l, κ l (p.2 l)) * |(stateCount p.2 p.1 : ℝ) / (N:ℝ) - φ p.1|
      = ∑ s' : Fin N → S, (∏ j, κ j (s' j)) *
          (∑ y, |(stateCount s' y : ℝ) / (N : ℝ) - φ y|) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' _ => ?_
    simp only [Finset.mul_sum]
  calc ∑ s' : Fin N → S, (∏ j, κ j (s' j)) *
          (∑ y, |(stateCount s' y : ℝ) / (N : ℝ) - φ y|)
      = ∑ p : S × (Fin N → S), Real.sqrt (∏ l, κ l (p.2 l)) *
          Real.sqrt ((∏ l, κ l (p.2 l)) *
            ((stateCount p.2 p.1 : ℝ) / (N:ℝ) - φ p.1) ^ 2) := by
        rw [← hL]
        exact (Finset.sum_congr rfl fun p _ => hterm p).symm
    _ ≤ Real.sqrt (∑ p : S × (Fin N → S), (∏ l, κ l (p.2 l))) *
          Real.sqrt (∑ p : S × (Fin N → S),
            (∏ l, κ l (p.2 l)) * ((stateCount p.2 p.1 : ℝ) / (N:ℝ) - φ p.1) ^ 2) := hCS
    _ ≤ Real.sqrt (Fintype.card S : ℝ) * Real.sqrt (1 / (N:ℝ)) := by
        rw [hf]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hgle) (Real.sqrt_nonneg _)
    _ = Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ)) := by
        rw [← Real.sqrt_mul (by positivity)]
        congr 1
        ring

/-! ### Index policies activate a deterministic number of agents in each local state -/

/-- The number of agents sitting in state `x` that the joint action `a` activates. -/
def cnt {N : ℕ} (st : Fin N → S) (a : Fin N → Bool) (x : S) : ℕ :=
  (Finset.univ.filter fun i => st i = x ∧ a i = true).card

theorem sum_cnt {N : ℕ} (st : Fin N → S) (a : Fin N → Bool) :
    ∑ x, cnt st a x = (Finset.univ.filter fun i => a i = true).card := by
  classical
  unfold cnt
  rw [Finset.card_eq_sum_card_fiberwise (f := st) (t := (Finset.univ : Finset S))
    (fun i _ => Finset.mem_univ (st i))]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

theorem count_mul_prob {N : ℕ} (ν : S → ℝ) (M : ℕ) (st : Fin N → S) (x : S) :
    (stateCount st x : ℝ) * indexActivationProb ν M st x = (activateCount ν M st x : ℝ) := by
  unfold indexActivationProb activateCount
  split_ifs with h
  · rw [h]; simp
  · have hne : ((stateCount st x : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 h
    field_simp

theorem expect_cnt {N : ℕ} (ν : S → ℝ) (M : ℕ) (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (hπ : IsIndexPolicy ν M π) (st : Fin N → S) (x : S) :
    ∑ a : Fin N → Bool, π st a * (cnt st a x : ℝ) = (activateCount ν M st x : ℝ) := by
  classical
  have hcnt : ∀ a : Fin N → Bool, (cnt st a x : ℝ)
      = ∑ i, (if st i = x then (if a i = true then (1:ℝ) else 0) else 0) := by
    intro a
    unfold cnt
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : st i = x <;> by_cases h2 : a i = true <;> simp [h1, h2]
  calc ∑ a : Fin N → Bool, π st a * (cnt st a x : ℝ)
      = ∑ a : Fin N → Bool, ∑ i,
          (if st i = x then (if a i = true then π st a else 0) else 0) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hcnt a, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h1 : st i = x <;> by_cases h2 : a i = true <;> simp [h1, h2]
    _ = ∑ i, ∑ a : Fin N → Bool,
          (if st i = x then (if a i = true then π st a else 0) else 0) := Finset.sum_comm
    _ = ∑ i, (if st i = x then indexActivationProb ν M st x else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h1 : st i = x
        · simp only [if_pos h1]
          rw [← h1]
          exact hπ.2.2 st i
        · simp [h1]
    _ = (activateCount ν M st x : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        exact count_mul_prob ν M st x

/-- An agent whose activation probability is one is activated by every action in the support. -/
theorem support_true {N : ℕ} (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (hnn : ∀ st a, 0 ≤ π st a) (hsum : ∀ st, ∑ a, π st a = 1)
    (st : Fin N → S) (i : Fin N)
    (h : ∑ a : Fin N → Bool, (if a i = true then π st a else 0) = 1)
    (a : Fin N → Bool) (ha : π st a ≠ 0) : a i = true := by
  classical
  by_contra hcon
  have hzero : ∑ b : Fin N → Bool, (if b i = true then 0 else π st b) = 0 := by
    have hsplit : ∀ b : Fin N → Bool,
        (if b i = true then π st b else 0) + (if b i = true then 0 else π st b) = π st b := by
      intro b
      by_cases hb : b i = true <;> simp [hb]
    have := Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => hsplit b)
    rw [Finset.sum_add_distrib, h, hsum st] at this
    linarith
  have hnn' : ∀ b ∈ (Finset.univ : Finset (Fin N → Bool)),
      0 ≤ (if b i = true then 0 else π st b) := by
    intro b _
    by_cases hb : b i = true <;> simp [hb, hnn st b]
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn').1 hzero a (Finset.mem_univ a)
  rw [if_neg hcon] at this
  exact ha this

/-- An agent whose activation probability is zero is never activated in the support. -/
theorem support_false {N : ℕ} (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (hnn : ∀ st a, 0 ≤ π st a) (st : Fin N → S) (i : Fin N)
    (h : ∑ a : Fin N → Bool, (if a i = true then π st a else 0) = 0)
    (a : Fin N → Bool) (ha : π st a ≠ 0) : a i = false := by
  classical
  by_contra hcon
  have htrue : a i = true := by simpa using hcon
  have hnn' : ∀ b ∈ (Finset.univ : Finset (Fin N → Bool)),
      0 ≤ (if b i = true then π st b else 0) := by
    intro b _
    by_cases hb : b i = true <;> simp [hb, hnn st b]
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn').1 h a (Finset.mem_univ a)
  rw [if_pos htrue] at this
  exact ha this

/-- The activated counts add up to the budget. -/
theorem sum_activateCount {N : ℕ} (ν : S → ℝ) (M : ℕ)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ) (hπ : IsIndexPolicy ν M π) (st : Fin N → S) :
    ∑ x, activateCount ν M st x = M := by
  classical
  have hR : ((∑ x, activateCount ν M st x : ℕ) : ℝ) = (M : ℝ) := by
    push_cast
    calc ∑ x, (activateCount ν M st x : ℝ)
        = ∑ x, ∑ a : Fin N → Bool, π st a * (cnt st a x : ℝ) :=
          (Finset.sum_congr rfl fun x _ => expect_cnt ν M π hπ st x).symm
      _ = ∑ a : Fin N → Bool, ∑ x, π st a * (cnt st a x : ℝ) := Finset.sum_comm
      _ = ∑ a : Fin N → Bool, π st a * ((Finset.univ.filter fun i => a i = true).card : ℝ) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Finset.mul_sum]
          congr 1
          rw [← Nat.cast_sum, sum_cnt]
      _ = ∑ a : Fin N → Bool, π st a * (M : ℝ) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          by_cases ha : π st a = 0
          · rw [ha]; ring
          · rw [hπ.2.1 st a ha]
      _ = (M : ℝ) := by rw [← Finset.sum_mul, hπ.1.2 st, one_mul]
  exact_mod_cast hR

/-- If `x` has strictly lower priority than `y`, the count above `y` together with `y` itself
is part of the count above `x`. -/
theorem hpc_add_le {N : ℕ} (ν : S → ℝ) (st : Fin N → S) {x y : S} (hxy : ν x < ν y) :
    higherPriorityCount ν st y + stateCount st y ≤ higherPriorityCount ν st x := by
  classical
  unfold higherPriorityCount
  have hy : y ∉ Finset.univ.filter (fun z => ν y < ν z) := by simp
  rw [add_comm, ← Finset.sum_insert hy]
  refine Finset.sum_le_sum_of_subset ?_
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  rcases hz with rfl | hz
  · exact hxy
  · exact hxy.trans hz

/-- At most one local state is served fractionally. -/
theorem frac_unique {N : ℕ} (ν : S → ℝ) (M : ℕ) (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (hπ : IsIndexPolicy ν M π) (st : Fin N → S) {x y : S}
    (hx : 0 < activateCount ν M st x ∧ activateCount ν M st x < stateCount st x)
    (hy : 0 < activateCount ν M st y ∧ activateCount ν M st y < stateCount st y) : x = y := by
  classical
  by_contra hne
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hax : activateCount ν M st x
      = min (stateCount st x) (M - higherPriorityCount ν st x) := rfl
  have hay : activateCount ν M st y
      = min (stateCount st y) (M - higherPriorityCount ν st y) := rfl
  have hcx1 : activateCount ν M st x = M - higherPriorityCount ν st x := by omega
  have hcx2 : higherPriorityCount ν st x < M := by omega
  have hcy1 : activateCount ν M st y = M - higherPriorityCount ν st y := by omega
  have hcy2 : higherPriorityCount ν st y < M := by omega
  rcases lt_trichotomy (ν x) (ν y) with hlt | heq | hgt
  · have h := hpc_add_le ν st hlt
    omega
  · have hfil : (Finset.univ.filter fun z => ν x < ν z)
        = (Finset.univ.filter fun z => ν y < ν z) := by
      ext z
      simp [heq]
    have hhx : higherPriorityCount ν st x = higherPriorityCount ν st y := by
      unfold higherPriorityCount
      rw [hfil]
    have hA : ∀ z ∈ Finset.univ.filter (fun z => ν x < ν z),
        activateCount ν M st z = stateCount st z := by
      intro z hz
      have hzx : ν x < ν z := (Finset.mem_filter.1 hz).2
      have h := hpc_add_le ν st hzx
      have haz : activateCount ν M st z
          = min (stateCount st z) (M - higherPriorityCount ν st z) := rfl
      omega
    have hsumA : ∑ z ∈ Finset.univ.filter (fun z => ν x < ν z), activateCount ν M st z
        = higherPriorityCount ν st x := by
      rw [Finset.sum_congr rfl hA]
      rfl
    have hxA : x ∉ Finset.univ.filter (fun z => ν x < ν z) := by simp
    have hyA : y ∉ Finset.univ.filter (fun z => ν x < ν z) := by simp [heq]
    have hxins : x ∉ insert y (Finset.univ.filter fun z => ν x < ν z) := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨hne, hxA⟩
    have hbig : ∑ z ∈ insert x (insert y (Finset.univ.filter fun z => ν x < ν z)),
        activateCount ν M st z ≤ ∑ z, activateCount ν M st z :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [Finset.sum_insert hxins, Finset.sum_insert hyA, hsumA,
      sum_activateCount ν M π hπ st] at hbig
    omega
  · have h := hpc_add_le ν st hgt
    omega

/-- Under an index policy the number of activated agents in each local state is the same for
every action in the policy's support: it is `activateCount`. -/
theorem cnt_eq {N : ℕ} (ν : S → ℝ) (M : ℕ) (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (hπ : IsIndexPolicy ν M π) (st : Fin N → S) (a : Fin N → Bool) (ha : π st a ≠ 0) (x : S) :
    cnt st a x = activateCount ν M st x := by
  classical
  have hdet : ∀ z : S, ¬(0 < activateCount ν M st z ∧ activateCount ν M st z < stateCount st z) →
      cnt st a z = activateCount ν M st z := by
    intro z hz
    have haz : activateCount ν M st z
        = min (stateCount st z) (M - higherPriorityCount ν st z) := rfl
    have hle : activateCount ν M st z ≤ stateCount st z := by omega
    rcases Nat.eq_zero_or_pos (stateCount st z) with hn | hn
    · have hc : activateCount ν M st z = 0 := by omega
      have hz0 : cnt st a z = 0 := by
        unfold cnt
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        have hmem : i ∈ Finset.univ.filter (fun i => st i = z) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hi.1
        have hn' : (Finset.univ.filter fun i => st i = z) = ∅ := by
          rw [← Finset.card_eq_zero]
          exact hn
        rw [hn'] at hmem
        simp at hmem
      omega
    · have hq := hπ.2.2 st
      rcases Nat.lt_or_ge (activateCount ν M st z) (stateCount st z) with hlt | hge
      · have hc0 : activateCount ν M st z = 0 := by omega
        have hprob : indexActivationProb ν M st z = 0 := by
          unfold indexActivationProb
          rw [if_neg (by omega), hc0]
          simp
        have hall : ∀ i, st i = z → a i = false := by
          intro i hi
          refine support_false π hπ.1.1 st i ?_ a ha
          have hqi := hq i
          rw [hi, hprob] at hqi
          exact hqi
        have hz0 : cnt st a z = 0 := by
          unfold cnt
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          rw [hall i hi.1] at hi
          simp at hi
        omega
      · have hcn : activateCount ν M st z = stateCount st z := le_antisymm hle hge
        have hprob : indexActivationProb ν M st z = 1 := by
          unfold indexActivationProb
          rw [if_neg (by omega), hcn]
          field_simp
        have hall : ∀ i, st i = z → a i = true := by
          intro i hi
          refine support_true π hπ.1.1 hπ.1.2 st i ?_ a ha
          have hqi := hq i
          rw [hi, hprob] at hqi
          exact hqi
        have hzn : cnt st a z = stateCount st z := by
          unfold cnt stateCount
          congr 1
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => h.1, fun h => ⟨h, hall i h⟩⟩
        omega
  by_cases hx : 0 < activateCount ν M st x ∧ activateCount ν M st x < stateCount st x
  · have hother : ∀ z ∈ Finset.univ.erase x, cnt st a z = activateCount ν M st z := by
      intro z hz
      refine hdet z ?_
      intro hfz
      exact (Finset.ne_of_mem_erase hz) (frac_unique ν M π hπ st hfz hx)
    have h1 : ∑ z, cnt st a z = ∑ z, activateCount ν M st z := by
      rw [sum_cnt, hπ.2.1 st a ha, sum_activateCount ν M π hπ st]
    have h2 : cnt st a x + ∑ z ∈ Finset.univ.erase x, cnt st a z
        = activateCount ν M st x + ∑ z ∈ Finset.univ.erase x, activateCount ν M st z := by
      rw [Finset.add_sum_erase _ (fun z => cnt st a z) (Finset.mem_univ x),
        Finset.add_sum_erase _ (fun z => activateCount ν M st z) (Finset.mem_univ x)]
      exact h1
    have h3 : ∑ z ∈ Finset.univ.erase x, cnt st a z
        = ∑ z ∈ Finset.univ.erase x, activateCount ν M st z := Finset.sum_congr rfl hother
    omega
  · exact hdet x hx

/-! ### Assembling the one-step bound -/

theorem fiber_sum {N : ℕ} (st : Fin N → S) (F : S → ℝ) :
    ∑ j, F (st j) = ∑ x, (stateCount st x : ℝ) * F x := by
  classical
  have h1 : ∀ j : Fin N, F (st j) = ∑ x, (if st j = x then F x else 0) := by
    intro j
    rw [Finset.sum_ite_eq Finset.univ (st j) F]
    simp
  rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rfl

theorem fiber_sum_act {N : ℕ} (st : Fin N → S) (a : Fin N → Bool) (F : S → ℝ) :
    ∑ j, (if a j = true then F (st j) else 0) = ∑ x, (cnt st a x : ℝ) * F x := by
  classical
  have h1 : ∀ j : Fin N, (if a j = true then F (st j) else 0)
      = ∑ x, (if st j = x ∧ a j = true then F x else 0) := by
    intro j
    by_cases h : a j = true
    · have hx : ∀ x : S, (if st j = x ∧ a j = true then F x else 0)
          = (if st j = x then F x else 0) := by
        intro x
        by_cases hxx : st j = x <;> simp [hxx, h]
      rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_ite_eq Finset.univ (st j) F]
      simp [h]
    · have hx : ∀ x : S, (if st j = x ∧ a j = true then F x else 0) = 0 := by
        intro x; simp [h]
      rw [Finset.sum_congr rfl (fun x _ => hx x)]
      simp [h]
  rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rfl

theorem hpm_eq {N : ℕ} (ν : S → ℝ) (st : Fin N → S) (x : S) :
    higherPriorityMass ν (configuration st) x = (higherPriorityCount ν st x : ℝ) / (N : ℝ) := by
  unfold higherPriorityMass higherPriorityCount configuration
  rw [Nat.cast_sum, Finset.sum_div]

theorem activateFraction_eq {N : ℕ} (ν : S → ℝ) (M : ℕ) (hN : 0 < N) (st : Fin N → S) (x : S) :
    activateFraction ν ((M : ℝ) / (N : ℝ)) (configuration st) x
      = (activateCount ν M st x : ℝ) / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  unfold activateFraction
  rw [hpm_eq, div_sub_div_same]
  unfold configuration activateCount
  rcases le_total (higherPriorityCount ν st x) M with hle | hge
  · have h1 : (0 : ℝ) ≤ ((M : ℝ) - (higherPriorityCount ν st x : ℝ)) / (N : ℝ) := by
      have : ((higherPriorityCount ν st x : ℝ)) ≤ (M : ℝ) := by exact_mod_cast hle
      positivity
    rw [max_eq_right h1, min_div_div_right hNpos.le]
    congr 1
    rw [Nat.cast_min, Nat.cast_sub hle]
  · have h0 : M - higherPriorityCount ν st x = 0 := Nat.sub_eq_zero_of_le hge
    have h1 : ((M : ℝ) - (higherPriorityCount ν st x : ℝ)) / (N : ℝ) ≤ 0 := by
      have : (M : ℝ) ≤ (higherPriorityCount ν st x : ℝ) := by exact_mod_cast hge
      apply div_nonpos_of_nonpos_of_nonneg <;> linarith
    rw [max_eq_left h1, h0]
    simp
    positivity

theorem kernel_sum_eq {N : ℕ} (P0 P1 : Matrix S S ℝ) (ν : S → ℝ) (M : ℕ) (hN : 0 < N)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ) (hπ : IsIndexPolicy ν M π)
    (st : Fin N → S) (a : Fin N → Bool) (ha : π st a ≠ 0) (y : S) :
    ∑ j, rmabKernel P0 P1 (st j) (a j) y
      = (N : ℝ) * meanFieldMap P0 P1 ν ((M : ℝ) / (N : ℝ)) (configuration st) y := by
  classical
  have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hsplit : ∀ j : Fin N, rmabKernel P0 P1 (st j) (a j) y
      = P0 (st j) y + (if a j = true then (P1 (st j) y - P0 (st j) y) else 0) := by
    intro j
    unfold rmabKernel
    by_cases h : a j = true <;> simp [h]
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib,
    fiber_sum st (fun x => P0 x y), fiber_sum_act st a (fun x => P1 x y - P0 x y)]
  simp only [meanFieldMap]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [activateFraction_eq ν M hN st x, cnt_eq ν M π hπ st a ha x]
  unfold configuration
  field_simp
  ring

open MarkovEntanglement in
theorem one_step {N : ℕ} (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0)
    (hP1 : IsTransitionMatrix P1) (ν : S → ℝ) (α : ℝ) (hN : 0 < N)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (hπ : IsIndexPolicy ν ⌊α * (N : ℝ)⌋₊ π) (st : Fin N → S) :
    ∑ s' : Fin N → S, rmabStep P0 P1 π st s' *
        l1Norm (fun x => configuration s' x
          - meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ)) (configuration st) x)
      ≤ Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ)) := by
  classical
  set M : ℕ := ⌊α * (N : ℝ)⌋₊ with hM
  set φ : S → ℝ := meanFieldMap P0 P1 ν ((M : ℝ) / (N : ℝ)) (configuration st) with hφdef
  have hswap : ∑ s' : Fin N → S, rmabStep P0 P1 π st s' *
        l1Norm (fun x => configuration s' x - φ x)
      = ∑ a : Fin N → Bool, π st a *
          ∑ s' : Fin N → S, (∏ j, rmabKernel P0 P1 (st j) (a j) (s' j)) *
            (∑ x, |(stateCount s' x : ℝ) / (N : ℝ) - φ x|) := by
    simp only [rmabStep, l1Norm, configuration]
    have h1 : ∀ s' : Fin N → S,
        (∑ a : Fin N → Bool, π st a * ∏ j, rmabKernel P0 P1 (st j) (a j) (s' j)) *
          (∑ x, |(stateCount s' x : ℝ) / (N:ℝ) - φ x|)
        = ∑ a : Fin N → Bool, π st a * ((∏ j, rmabKernel P0 P1 (st j) (a j) (s' j)) *
            (∑ x, |(stateCount s' x : ℝ) / (N:ℝ) - φ x|)) := by
      intro s'
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [Finset.sum_congr rfl (fun s' _ => h1 s'), Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
  rw [hswap]
  have hterm : ∀ a : Fin N → Bool, π st a *
      (∑ s' : Fin N → S, (∏ j, rmabKernel P0 P1 (st j) (a j) (s' j)) *
        (∑ x, |(stateCount s' x : ℝ) / (N : ℝ) - φ x|))
      ≤ π st a * Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ)) := by
    intro a
    by_cases ha : π st a = 0
    · rw [ha]; simp
    · refine mul_le_mul_of_nonneg_left ?_ (hπ.1.1 st a)
      refine cond_bound hN (fun j y => rmabKernel P0 P1 (st j) (a j) y) ?_ ?_ φ ?_
      · intro j y
        unfold rmabKernel
        by_cases h : a j = true <;> simp [h, hP0.1, hP1.1]
      · intro j
        unfold rmabKernel
        by_cases h : a j = true <;> simp [h, hP0.2, hP1.2]
      · intro y
        exact kernel_sum_eq P0 P1 ν M hN π hπ st a ha y
  calc ∑ a : Fin N → Bool, π st a *
        (∑ s' : Fin N → S, (∏ j, rmabKernel P0 P1 (st j) (a j) (s' j)) *
          (∑ x, |(stateCount s' x : ℝ) / (N : ℝ) - φ x|))
      ≤ ∑ a : Fin N → Bool, π st a * Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ)) :=
        Finset.sum_le_sum fun a _ => hterm a
    _ = Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ)) := by
        rw [← Finset.sum_mul, hπ.1.2 st, one_mul]

end ME9

open MarkovEntanglement ME9 in
theorem solution {S : Type*} [Fintype S] [DecidableEq S]
    (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (ν : S → ℝ) (α : ℝ) (N : ℕ) (hN : 0 < N)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (hπ : IsIndexPolicy ν ⌊α * (N : ℝ)⌋₊ π)
    (s : Fin N → S) :
    ∑ s' : Fin N → S, rmabStep P0 P1 π s s' *
        l1Norm (fun x => configuration s' x
          - meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ)) (configuration s) x)
      ≤ Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ)) :=
  ME9.one_step P0 P1 hP0 hP1 ν α hN π hπ s
