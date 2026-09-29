-- Prove2me | solution 1 for MarkovMixing.riffle_mixing_lower
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-23T05:00:58.816646+00:00
-- url     : https://prove2.me/submissions/0120ffcc-fe78-4f53-bb4b-a037814d25f3

import Definitions.Def_mm_shuffle
import Theorems.Thm_MarkovMixing_counting_lower_bound
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.GroupTheory.Perm.Sign

/-!
# A lower bound for the riffle shuffle (LPW Proposition 8.14)
-/

namespace MarkovMixing

noncomputable section
open scoped BigOperators
open Finset

section Riffle

variable {n : ℕ}

private lemma riffle_apply (x y : Equiv.Perm (Fin n)) :
    riffleShuffle n x y
      = (((univ.filter fun d : Fin n → Bool => x * (Tuple.sort d)⁻¹ = y).card : ℕ) : ℝ)
          / 2 ^ n := by
  rw [riffleShuffle, inverseRiffle]
  congr 2
  refine Finset.card_nbij' (fun b : Fin n → Bool => fun p : Fin n => b (y p))
    (fun d : Fin n → Bool => fun v : Fin n => d (y.symm v)) ?_ ?_ ?_ ?_
  · intro b hb
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hb ⊢
    refine Equiv.ext fun q => ?_
    have h := hb ((Tuple.sort (fun p : Fin n => b (y p)))⁻¹ q)
    rw [Equiv.Perm.mul_apply, h]
    simp
  · intro d hd
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hd ⊢
    intro q
    have hfun : (fun p : Fin n => (fun v : Fin n => d (y.symm v)) (y p)) = d := by
      funext p
      simp
    rw [hfun]
    have h := congrFun (congrArg (fun (e : Equiv.Perm (Fin n)) => (e : Fin n → Fin n)) hd)
      (Tuple.sort d q)
    simp only [Equiv.Perm.coe_mul, Function.comp_apply] at h
    rw [← h]
    simp
  · intro b _
    funext v
    simp
  · intro d _
    funext p
    simp

private lemma sum_div_const {α : Type*} (s : Finset α) (f : α → ℝ) (c : ℝ) :
    (∑ i ∈ s, f i) / c = ∑ i ∈ s, f i / c := by
  simp [div_eq_mul_inv, Finset.sum_mul]

private lemma card_bool_fun : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
  rw [Finset.card_univ, Fintype.card_fun]
  simp

private lemma riffle_nonneg (x y : Equiv.Perm (Fin n)) : 0 ≤ riffleShuffle n x y := by
  rw [riffle_apply]
  positivity

private lemma riffle_pos_of (x : Equiv.Perm (Fin n)) (d : Fin n → Bool) :
    0 < riffleShuffle n x (x * (Tuple.sort d)⁻¹) := by
  rw [riffle_apply]
  refine div_pos ?_ (by positivity)
  have hmem : d ∈ univ.filter fun e : Fin n → Bool => x * (Tuple.sort e)⁻¹
      = x * (Tuple.sort d)⁻¹ := by
    simp
  have : 0 < (univ.filter fun e : Fin n → Bool => x * (Tuple.sort e)⁻¹
      = x * (Tuple.sort d)⁻¹).card := Finset.card_pos.mpr ⟨d, hmem⟩
  exact_mod_cast this

private lemma riffle_stochastic : IsStochastic (riffleShuffle n) := by
  refine ⟨riffle_nonneg, fun x => ?_⟩
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun d : Fin n → Bool => x * (Tuple.sort d)⁻¹)
    (s := (Finset.univ : Finset (Fin n → Bool)))
    (t := (Finset.univ : Finset (Equiv.Perm (Fin n))))
    (fun d _ => Finset.mem_univ _)
  rw [card_bool_fun] at hfib
  rw [Finset.sum_congr rfl fun y _ => riffle_apply x y, ← sum_div_const]
  have hcast : ∑ y : Equiv.Perm (Fin n),
      (((univ.filter fun d : Fin n → Bool => x * (Tuple.sort d)⁻¹ = y).card : ℕ) : ℝ)
      = ((2 ^ n : ℕ) : ℝ) := by
    rw [← Nat.cast_sum, ← hfib]
  rw [hcast]
  push_cast
  rw [div_self (by positivity)]

private lemma riffle_col_sum (y : Equiv.Perm (Fin n)) :
    ∑ x : Equiv.Perm (Fin n), riffleShuffle n x y = 1 := by
  have hcount : ∀ x : Equiv.Perm (Fin n),
      ((univ.filter fun d : Fin n → Bool => x * (Tuple.sort d)⁻¹ = y).card : ℕ)
        = ∑ d : Fin n → Bool, (if x = y * Tuple.sort d then 1 else 0) := by
    intro x
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    congr 1
    simp only [eq_iff_iff]
    constructor
    · intro h
      rw [← h]
      group
    · intro h
      rw [h]
      group
  rw [Finset.sum_congr rfl fun x _ => riffle_apply x y, ← sum_div_const]
  have hsum : ∑ x : Equiv.Perm (Fin n),
      (((univ.filter fun d : Fin n → Bool => x * (Tuple.sort d)⁻¹ = y).card : ℕ) : ℝ)
      = (2 : ℝ) ^ n := by
    rw [Finset.sum_congr rfl fun x _ => by rw [hcount x]]
    push_cast
    rw [Finset.sum_comm]
    have hinner : ∀ d : Fin n → Bool,
        (∑ x : Equiv.Perm (Fin n), (if x = y * Tuple.sort d then (1:ℝ) else 0)) = 1 := by
      intro d
      rw [Finset.sum_ite_eq' Finset.univ (y * Tuple.sort d) (fun _ => (1:ℝ))]
      simp
    rw [Finset.sum_congr rfl fun d _ => hinner d, Finset.sum_const, card_bool_fun,
      nsmul_eq_mul, mul_one]
    push_cast
    ring
  rw [hsum, div_self (by positivity)]

private lemma riffle_stationary :
    IsStationary (riffleShuffle n) (uniformDist (Equiv.Perm (Fin n))) := by
  have hN : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
    have : 0 < Fintype.card (Equiv.Perm (Fin n)) := Fintype.card_pos
    exact_mod_cast this
  refine ⟨⟨fun x => by simp only [uniformDist]; positivity, ?_⟩, ?_⟩
  · simp only [uniformDist]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  · ext y
    simp only [Matrix.vecMul, dotProduct, uniformDist]
    rw [← Finset.mul_sum, riffle_col_sum, mul_one]

/-! ### Two special riffle moves -/

private lemma sort_const_false (n : ℕ) : Tuple.sort (fun _ : Fin n => false) = 1 := by
  have h : Tuple.sort (fun _ : Fin n => false) = Equiv.refl _ :=
    Tuple.sort_eq_refl_iff_monotone.mpr (fun a b _ => le_refl _)
  rw [h]
  rfl

private def adjBits {m : ℕ} (i : Fin m) : Fin (m + 1) → Bool :=
  fun p => decide (p.val = i.val ∨ i.val + 1 < p.val)

private lemma adjBits_iff {m : ℕ} (i : Fin m) (p : Fin (m + 1)) :
    adjBits i p = true ↔ (p.val = i.val ∨ i.val + 1 < p.val) := by
  rw [adjBits]
  simp

private lemma swap_val {m : ℕ} (i : Fin m) (p : Fin (m + 1)) :
    ((Equiv.swap i.castSucc i.succ) p).val
      = if p.val = i.val then i.val + 1 else if p.val = i.val + 1 then i.val else p.val := by
  have hcs : (i.castSucc : Fin (m + 1)).val = i.val := rfl
  have hsc : (i.succ : Fin (m + 1)).val = i.val + 1 := rfl
  by_cases h1 : p = i.castSucc
  · rw [h1, Equiv.swap_apply_left, hsc, hcs, if_pos rfl]
  · by_cases h2 : p = i.succ
    · rw [h2, Equiv.swap_apply_right, hcs, hsc]
      rw [if_neg (by omega), if_pos rfl]
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      have hv1 : p.val ≠ i.val := fun hc => h1 (Fin.ext (by rw [hc, hcs]))
      have hv2 : p.val ≠ i.val + 1 := fun hc => h2 (Fin.ext (by rw [hc, hsc]))
      rw [if_neg hv1, if_neg hv2]

private lemma adjBits_swap {m : ℕ} (i : Fin m) (p : Fin (m + 1)) :
    adjBits i ((Equiv.swap i.castSucc i.succ) p) = true ↔ i.val + 1 ≤ p.val := by
  rw [adjBits_iff, swap_val]
  have hlt : i.val < m + 1 := by omega
  by_cases h1 : p.val = i.val
  · rw [if_pos h1]
    constructor
    · intro _
      omega
    · intro h
      omega
  · rw [if_neg h1]
    by_cases h2 : p.val = i.val + 1
    · rw [if_pos h2]
      constructor
      · intro _
        omega
      · intro _
        left
        rfl
    · rw [if_neg h2]
      constructor
      · intro h
        rcases h with h | h <;> omega
      · intro h
        right
        omega

private lemma sort_adjBits {m : ℕ} (i : Fin m) :
    Tuple.sort (adjBits i) = Equiv.swap i.castSucc i.succ := by
  refine (Tuple.eq_sort_iff.mpr ⟨?_, ?_⟩).symm
  · intro a b hab
    have habv : a.val ≤ b.val := hab
    simp only [Function.comp_apply]
    by_cases h : adjBits i ((Equiv.swap i.castSucc i.succ) a) = true
    · have h1 := (adjBits_swap i a).mp h
      have h2 : i.val + 1 ≤ b.val := le_trans h1 habv
      rw [h, (adjBits_swap i b).mpr h2]
    · rw [Bool.not_eq_true] at h
      rw [h]
      exact Bool.false_le _
  · intro a b hab heq
    have hab' : a.val < b.val := hab
    rw [Fin.lt_def, swap_val, swap_val]
    by_cases h : adjBits i ((Equiv.swap i.castSucc i.succ) a) = true
    · have ha : i.val + 1 ≤ a.val := (adjBits_swap i a).mp h
      have hb : i.val + 1 ≤ b.val := (adjBits_swap i b).mp (by rw [← heq]; exact h)
      split_ifs <;> omega
    · rw [Bool.not_eq_true] at h
      have ha : ¬ (i.val + 1 ≤ a.val) := by
        intro hc
        rw [(adjBits_swap i a).mpr hc] at h
        exact Bool.noConfusion h
      have hb : ¬ (i.val + 1 ≤ b.val) := by
        intro hc
        have hbt : adjBits i ((Equiv.swap i.castSucc i.succ) b) = true :=
          (adjBits_swap i b).mpr hc
        rw [← heq, h] at hbt
        exact Bool.noConfusion hbt
      split_ifs <;> omega


/-! ### The riffle shuffle is an irreducible aperiodic random walk -/

private lemma riffle_transl (z a b : Equiv.Perm (Fin n)) :
    riffleShuffle n (z * a) (z * b) = riffleShuffle n a b := by
  rw [riffle_apply, riffle_apply]
  have hset : (univ.filter fun d : Fin n → Bool => (z * a) * (Tuple.sort d)⁻¹ = z * b)
      = (univ.filter fun d : Fin n → Bool => a * (Tuple.sort d)⁻¹ = b) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mul_assoc, mul_right_inj]
  rw [hset]

private lemma riffle_pow_nonneg : ∀ (t : ℕ) (a b : Equiv.Perm (Fin n)),
    0 ≤ ((riffleShuffle n) ^ t) a b := by
  intro t
  induction t with
  | zero => intro a b; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ t ih =>
      intro a b
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun w _ => mul_nonneg (ih a w) (riffle_nonneg w b)

private lemma riffle_pow_transl : ∀ (t : ℕ) (z a b : Equiv.Perm (Fin n)),
    ((riffleShuffle n) ^ t) (z * a) (z * b) = ((riffleShuffle n) ^ t) a b := by
  intro t
  induction t with
  | zero =>
      intro z a b
      rw [pow_zero, Matrix.one_apply, Matrix.one_apply]
      by_cases h : a = b
      · rw [if_pos h, if_pos (by rw [h])]
      · rw [if_neg h, if_neg (fun hc => h (mul_left_cancel hc))]
  | succ t ih =>
      intro z a b
      have hL : ((riffleShuffle n) ^ (t + 1)) (z * a) (z * b)
          = ∑ w, ((riffleShuffle n) ^ t) (z * a) w * riffleShuffle n w (z * b) := by
        rw [pow_succ, Matrix.mul_apply]
      have hR : ((riffleShuffle n) ^ (t + 1)) a b
          = ∑ w, ((riffleShuffle n) ^ t) a w * riffleShuffle n w b := by
        rw [pow_succ, Matrix.mul_apply]
      rw [hL, hR]
      rw [← Equiv.sum_comp (Equiv.mulLeft z)
        (fun w => ((riffleShuffle n) ^ t) (z * a) w * riffleShuffle n w (z * b))]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [Equiv.coe_mulLeft]
      rw [ih z a w, riffle_transl]

private lemma riffle_pow_add_pos {t₁ t₂ : ℕ} {a b c : Equiv.Perm (Fin n)}
    (h1 : 0 < ((riffleShuffle n) ^ t₁) a b) (h2 : 0 < ((riffleShuffle n) ^ t₂) b c) :
    0 < ((riffleShuffle n) ^ (t₁ + t₂)) a c := by
  rw [pow_add, Matrix.mul_apply]
  refine lt_of_lt_of_le (mul_pos h1 h2) ?_
  exact Finset.single_le_sum
    (f := fun w => ((riffleShuffle n) ^ t₁) a w * ((riffleShuffle n) ^ t₂) w c)
    (fun w _ => mul_nonneg (riffle_pow_nonneg t₁ a w) (riffle_pow_nonneg t₂ w c))
    (Finset.mem_univ b)

private lemma reach_one : ∀ (n : ℕ) (g : Equiv.Perm (Fin n)),
    ∃ t : ℕ, 0 < ((riffleShuffle n) ^ t) 1 g := by
  intro n
  cases n with
  | zero =>
      intro g
      refine ⟨0, ?_⟩
      have hg : g = 1 := Subsingleton.elim _ _
      rw [pow_zero, hg, Matrix.one_apply_eq]
      norm_num
  | succ m =>
      intro g
      have hmem : g ∈ Submonoid.closure
          (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
        rw [Equiv.Perm.mclosure_swap_castSucc_succ]
        exact Submonoid.mem_top g
      refine Submonoid.closure_induction ?_ ?_ ?_ hmem
      · rintro x ⟨i, rfl⟩
        refine ⟨1, ?_⟩
        rw [pow_one]
        have h := riffle_pos_of (1 : Equiv.Perm (Fin (m + 1))) (adjBits i)
        rw [sort_adjBits, one_mul, Equiv.swap_inv] at h
        exact h
      · exact ⟨0, by rw [pow_zero, Matrix.one_apply_eq]; norm_num⟩
      · rintro a b - - ⟨t₁, h₁⟩ ⟨t₂, h₂⟩
        refine ⟨t₁ + t₂, ?_⟩
        have h₂' : 0 < ((riffleShuffle (m + 1)) ^ t₂) a (a * b) := by
          have := riffle_pow_transl t₂ a 1 b
          rw [mul_one] at this
          rw [this]
          exact h₂
        exact riffle_pow_add_pos h₁ h₂'

private lemma riffle_irreducible : Irreducible (riffleShuffle n) := by
  intro x y
  obtain ⟨t, ht⟩ := reach_one n (x⁻¹ * y)
  refine ⟨t, ?_⟩
  have h := riffle_pow_transl t x 1 (x⁻¹ * y)
  rw [mul_one, mul_inv_cancel_left] at h
  rw [h]
  exact ht

private lemma riffle_self_pos (x : Equiv.Perm (Fin n)) : 0 < riffleShuffle n x x := by
  have h := riffle_pos_of x (fun _ : Fin n => false)
  rw [sort_const_false, inv_one, mul_one] at h
  exact h

private lemma riffle_aperiodic : Aperiodic (riffleShuffle n) := by
  intro x
  have h1 : (1 : ℕ) ∈ returnSet (riffleShuffle n) x := by
    refine ⟨le_refl 1, ?_⟩
    rw [pow_one]
    exact riffle_self_pos x
  have hset : {d : ℕ | ∀ t ∈ returnSet (riffleShuffle n) x, d ∣ t} = {1} := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      exact Nat.dvd_one.mp (h 1 h1)
    · intro h t _
      rw [h]
      exact one_dvd t
  rw [period, hset, csSup_singleton]

private lemma outdeg_le (x : Equiv.Perm (Fin n)) :
    (univ.filter fun y => 0 < riffleShuffle n x y).card ≤ 2 ^ n := by
  have hsub : (univ.filter fun y : Equiv.Perm (Fin n) => 0 < riffleShuffle n x y)
      ⊆ Finset.image (fun d : Fin n → Bool => x * (Tuple.sort d)⁻¹) univ := by
    intro y hy
    rw [Finset.mem_filter] at hy
    have h := hy.2
    rw [riffle_apply] at h
    have hc : 0 < (univ.filter fun d : Fin n → Bool => x * (Tuple.sort d)⁻¹ = y).card := by
      by_contra hcon
      push_neg at hcon
      have hz : (univ.filter fun d : Fin n → Bool => x * (Tuple.sort d)⁻¹ = y).card = 0 :=
        Nat.le_zero.mp hcon
      rw [hz] at h
      norm_num at h
    obtain ⟨d, hd⟩ := Finset.card_pos.mp hc
    exact Finset.mem_image.mpr ⟨d, Finset.mem_univ d, (Finset.mem_filter.mp hd).2⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans Finset.card_image_le ?_
  rw [card_bool_fun]

private lemma maxOutDegree_le : maxOutDegree (riffleShuffle n) ≤ 2 ^ n := by
  rw [maxOutDegree]
  exact Finset.sup_le fun x _ => outdeg_le x

private lemma maxOutDegree_ge (hn : 2 ≤ n) : 2 ≤ maxOutDegree (riffleShuffle n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 0 < m := by omega
  set i : Fin m := ⟨0, hm⟩ with hi
  have hswap : (0 : ℝ) < riffleShuffle (m + 1) 1 (Equiv.swap i.castSucc i.succ) := by
    have h := riffle_pos_of (1 : Equiv.Perm (Fin (m + 1))) (adjBits i)
    rw [sort_adjBits, one_mul, Equiv.swap_inv] at h
    exact h
  have hne : (Equiv.swap i.castSucc i.succ : Equiv.Perm (Fin (m + 1))) ≠ 1 := by
    intro hc
    have := congrArg (fun (e : Equiv.Perm (Fin (m + 1))) => e i.castSucc) hc
    simp only [Equiv.swap_apply_left, Equiv.Perm.one_apply] at this
    exact absurd (congrArg Fin.val this) (by simp [Fin.val_succ])
  have hcard : 2 ≤ (univ.filter fun y : Equiv.Perm (Fin (m + 1)) =>
      0 < riffleShuffle (m + 1) 1 y).card := by
    refine Finset.one_lt_card.mpr ⟨1, ?_, Equiv.swap i.castSucc i.succ, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, riffle_self_pos 1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hswap⟩
    · exact fun hc => hne hc.symm
  refine le_trans hcard ?_
  rw [maxOutDegree]
  exact Finset.le_sup
    (f := fun x : Equiv.Perm (Fin (m + 1)) =>
      (univ.filter fun y : Equiv.Perm (Fin (m + 1)) => 0 < riffleShuffle (m + 1) x y).card)
    (Finset.mem_univ (1 : Equiv.Perm (Fin (m + 1))))

/-! ### A Stirling-type lower bound on `n!` -/

private lemma exp_ge_pow (n : ℕ) : ((n : ℝ) + 1) ^ n ≤ Real.exp 1 * (n : ℝ) ^ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp only [Nat.cast_zero, zero_add, one_pow, pow_zero, mul_one]
    exact Real.one_le_exp (by norm_num)
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
    have h1 : (1 : ℝ) + 1 / (n : ℝ) ≤ Real.exp (1 / (n : ℝ)) := by
      have := Real.add_one_le_exp (1 / (n : ℝ))
      linarith
    have h2 : ((1 : ℝ) + 1 / (n : ℝ)) ^ n ≤ (Real.exp (1 / (n : ℝ))) ^ n :=
      pow_le_pow_left₀ (by positivity) h1 n
    have h3 : (Real.exp (1 / (n : ℝ))) ^ n = Real.exp 1 := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    have h4 : ((n : ℝ) + 1) ^ n = ((1 : ℝ) + 1 / (n : ℝ)) ^ n * (n : ℝ) ^ n := by
      rw [← mul_pow]
      congr 1
      field_simp
    rw [h3] at h2
    rw [h4]
    exact mul_le_mul_of_nonneg_right h2 (by positivity)

private lemma factorial_lower (n : ℕ) :
    ((n : ℝ) ^ n) / Real.exp n ≤ (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hexp : (0 : ℝ) < Real.exp n := Real.exp_pos _
      have hexp1 : (0 : ℝ) < Real.exp ((n : ℝ) + 1) := Real.exp_pos _
      have hnn : (0 : ℝ) ≤ (n : ℝ) ^ n := by positivity
      have hkey : (((n : ℝ) + 1) ^ (n + 1)) / Real.exp ((n : ℝ) + 1)
          ≤ ((n : ℝ) + 1) * ((n : ℝ) ^ n / Real.exp n) := by
        rw [div_le_iff₀ hexp1]
        have hE : Real.exp ((n : ℝ) + 1) = Real.exp n * Real.exp 1 := by
          rw [← Real.exp_add]
        rw [hE]
        have hp := exp_ge_pow n
        have hstep : ((n : ℝ) + 1) ^ (n + 1) = ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ n := by ring
        rw [hstep]
        have hmul : ((n : ℝ) + 1) * (((n : ℝ) + 1) ^ n)
            ≤ ((n : ℝ) + 1) * (Real.exp 1 * (n : ℝ) ^ n) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
        have hfin : ((n : ℝ) + 1) * (Real.exp 1 * (n : ℝ) ^ n)
            = ((n : ℝ) + 1) * ((n : ℝ) ^ n / Real.exp n) * (Real.exp n * Real.exp 1) := by
          field_simp
          try ring
        rw [hfin] at hmul
        exact hmul
      have hfac : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast, hfac]
      refine le_trans hkey ?_
      exact mul_le_mul_of_nonneg_left ih (by positivity)

private lemma log_factorial_ge (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - (n : ℝ) ≤ Real.log (n.factorial : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) ^ n / Real.exp n := by positivity
  have hlog := Real.log_le_log hpos (factorial_lower n)
  refine le_trans (le_of_eq ?_) hlog
  rw [Real.log_div (by positivity) (ne_of_gt (Real.exp_pos _)), Real.log_pow, Real.log_exp]
  try ring

end Riffle

end

end MarkovMixing

open MarkovMixing

/-- **Proposition 8.14** (LPW): for the riffle shuffle on an `n`-card deck
and fixed `0 < ε, δ < 1`, for sufficiently large `n`,
`t_mix(ε) ≥ (1 − δ) log₂ n`. -/
theorem solution (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (1 - δ) * Real.logb 2 n ≤
        (mixingTime (riffleShuffle n) (uniformDist (Equiv.Perm (Fin n))) ε : ℝ) := by
  set L : ℝ := 1 - Real.log (1 - ε) with hL
  have hlogneg : Real.log (1 - ε) < 0 := Real.log_neg (by linarith) (by linarith)
  have hL1 : 1 ≤ L := by rw [hL]; linarith
  refine ⟨max 2 (⌈Real.exp (L / δ + L + 2)⌉₊ + 1), ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  -- `log n` is large
  have hlogn : L / δ + L + 2 ≤ Real.log n := by
    have h1 : Real.exp (L / δ + L + 2) ≤ (⌈Real.exp (L / δ + L + 2)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp (L / δ + L + 2)⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
      have := le_trans (le_max_right 2 (⌈Real.exp (L / δ + L + 2)⌉₊ + 1)) hn
      have h3 : (⌈Real.exp (L / δ + L + 2)⌉₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast this
      linarith
    have h4 : Real.exp (L / δ + L + 2) ≤ (n : ℝ) := le_trans h1 h2
    have := Real.log_le_log (Real.exp_pos _) h4
    rwa [Real.log_exp] at this
  have hLd : L ≤ δ * Real.log n := by
    have hdd : L / δ ≤ Real.log n := by linarith
    rw [div_le_iff₀ hδ] at hdd
    linarith
  have hlogn2 : L + 2 ≤ Real.log n := by
    have hd0 : (0 : ℝ) ≤ L / δ := by positivity
    linarith
  -- the numerator is nonnegative
  have hfacR : (0 : ℝ) < (n.factorial : ℝ) := by
    have : 0 < n.factorial := Nat.factorial_pos n
    exact_mod_cast this
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) = (n.factorial : ℝ) := by
    rw [Fintype.card_perm, Fintype.card_fin]
  have hlogfac := log_factorial_ge n (by omega)
  have hA0 : (0 : ℝ) ≤ Real.log ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (1 - ε)) := by
    rw [hcard, Real.log_mul (ne_of_gt hfacR) (by linarith)]
    have h1 : (n : ℝ) * (L + 2) ≤ (n : ℝ) * Real.log n :=
      mul_le_mul_of_nonneg_left hlogn2 hnR.le
    have h2 : Real.log (1 - ε) = 1 - L := by rw [hL]; ring
    nlinarith [hlogfac, hL1]
  -- the main comparison
  have hmain : (1 - δ) * Real.logb 2 n
      ≤ Real.log ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (1 - ε)) / ((n : ℝ) * Real.log 2) := by
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    rw [Real.logb, le_div_iff₀ (by positivity)]
    rw [hcard, Real.log_mul (ne_of_gt hfacR) (by linarith)]
    have h2 : Real.log (1 - ε) = 1 - L := by rw [hL]; ring
    have hnL : (n : ℝ) * L ≤ (n : ℝ) * (δ * Real.log n) :=
      mul_le_mul_of_nonneg_left hLd hnR.le
    have hsplit : (n : ℝ) - Real.log (1 - ε) ≤ (n : ℝ) * L := by
      rw [h2]
      nlinarith [hL1, hn1R]
    have hfinal : (1 - δ) * (n : ℝ) * Real.log n
        ≤ Real.log (n.factorial : ℝ) + Real.log (1 - ε) := by
      nlinarith [hlogfac, hnL, hsplit]
    calc (1 - δ) * (Real.log n / Real.log 2) * ((n : ℝ) * Real.log 2)
        = (1 - δ) * (n : ℝ) * Real.log n := by field_simp; try ring
      _ ≤ Real.log (n.factorial : ℝ) + Real.log (1 - ε) := hfinal
  -- the counting bound
  have hD2 : 2 ≤ maxOutDegree (riffleShuffle n) := maxOutDegree_ge hn2
  have hDle : maxOutDegree (riffleShuffle n) ≤ 2 ^ n := maxOutDegree_le
  have hlogD0 : (0 : ℝ) < Real.log (maxOutDegree (riffleShuffle n)) := by
    refine Real.log_pos ?_
    have : (2 : ℝ) ≤ (maxOutDegree (riffleShuffle n) : ℝ) := by exact_mod_cast hD2
    linarith
  have hlogDle : Real.log (maxOutDegree (riffleShuffle n)) ≤ (n : ℝ) * Real.log 2 := by
    have h1 : ((maxOutDegree (riffleShuffle n) : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
      exact_mod_cast hDle
    have h2 := Real.log_le_log (by
      have : (2 : ℝ) ≤ (maxOutDegree (riffleShuffle n) : ℝ) := by exact_mod_cast hD2
      linarith) h1
    rwa [Real.log_pow] at h2
  have hcb := counting_lower_bound (riffleShuffle n) riffle_stochastic riffle_irreducible
    riffle_aperiodic riffle_stationary ε hε hε1
  refine le_trans hmain (le_trans ?_ hcb)
  exact div_le_div_of_nonneg_left hA0 hlogD0 hlogDle
