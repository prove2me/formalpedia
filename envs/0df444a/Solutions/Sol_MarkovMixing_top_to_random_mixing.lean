-- Prove2me | solution 1 for MarkovMixing.top_to_random_mixing
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-23T10:00:31.101584+00:00
-- url     : https://prove2.me/submissions/c0cee80f-6fd4-487f-a9a4-b0e7c684dee3

import Definitions.Def_mm_stopping
import Theorems.Thm_MarkovMixing_top_to_random_strong_stationary
import Theorems.Thm_MarkovMixing_strong_stationary_bound
import Mathlib.GroupTheory.Perm.Closure
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Top-to-random: `d(⌈n log n + α n⌉) ≤ e^{-α}` (LPW §6.5.3)
-/

namespace MarkovMixing

noncomputable section
open scoped BigOperators
open Finset

section Tau

variable {n : ℕ}

/-- The position permutation realised by inserting the top card at slot `j`. -/
private def tauF (n : ℕ) (j : Fin n) : Fin n → Fin n := fun i =>
  if h : i.val < j.val then ⟨i.val + 1, by have := j.isLt; omega⟩
  else if i = j then ⟨0, i.pos⟩ else i

private def tauG (n : ℕ) (j : Fin n) : Fin n → Fin n := fun i =>
  if i.val = 0 then j
  else if i.val ≤ j.val then ⟨i.val - 1, by have := i.isLt; omega⟩ else i

private lemma tauG_tauF (j : Fin n) (i : Fin n) : tauG n j (tauF n j i) = i := by
  by_cases h1 : i.val < j.val
  · have e : tauF n j i = ⟨i.val + 1, by have := j.isLt; omega⟩ := by
      simp only [tauF]; rw [dif_pos h1]
    rw [e]
    simp only [tauG]
    rw [if_neg (by show ¬ (i.val + 1 = 0); omega),
      if_pos (by show i.val + 1 ≤ j.val; omega)]
    exact Fin.ext (by simp)
  · by_cases h2 : i = j
    · have e : tauF n j i = ⟨0, i.pos⟩ := by
        simp only [tauF]; rw [dif_neg h1, if_pos h2]
      rw [e]
      simp only [tauG]
      rw [if_pos trivial]
      exact h2.symm
    · have hgt : j.val < i.val := by
        rcases lt_trichotomy i.val j.val with h | h | h
        · exact absurd h h1
        · exact absurd (Fin.ext h) h2
        · exact h
      have e : tauF n j i = i := by
        simp only [tauF]; rw [dif_neg h1, if_neg h2]
      rw [e]
      simp only [tauG]
      rw [if_neg (by omega), if_neg (by omega)]

private lemma tauF_tauG (j : Fin n) (i : Fin n) : tauF n j (tauG n j i) = i := by
  by_cases h1 : i.val = 0
  · have e : tauG n j i = j := by simp only [tauG]; rw [if_pos h1]
    rw [e]
    simp only [tauF]
    rw [dif_neg (by omega), if_pos trivial]
    exact Fin.ext (by simp [h1])
  · by_cases h2 : i.val ≤ j.val
    · have e : tauG n j i = ⟨i.val - 1, by have := i.isLt; omega⟩ := by
        simp only [tauG]; rw [if_neg h1, if_pos h2]
      rw [e]
      simp only [tauF]
      rw [dif_pos (by show i.val - 1 < j.val; omega)]
      exact Fin.ext (by simp; omega)
    · have e : tauG n j i = i := by
        simp only [tauG]; rw [if_neg h1, if_neg h2]
      rw [e]
      simp only [tauF]
      rw [dif_neg (by omega), if_neg (by intro hc; rw [hc] at h2; omega)]

/-- Inserting the top card at slot `j` acts on positions by this permutation. -/
private def tau (n : ℕ) (j : Fin n) : Equiv.Perm (Fin n) :=
  { toFun := tauF n j, invFun := tauG n j,
    left_inv := tauG_tauF j, right_inv := tauF_tauG j }

private lemma tau_apply (j i : Fin n) : tau n j i = tauF n j i := rfl

private lemma insert_eq (x : Equiv.Perm (Fin n)) (j : Fin n) :
    topToRandomInsert x j = fun i => x (tau n j i) := by
  funext i
  show topToRandomInsert x j i = x (tauF n j i)
  unfold topToRandomInsert tauF
  split_ifs <;> rfl

private lemma tau_inj : Function.Injective (tau n) := by
  intro j j' h
  by_contra hne
  rcases lt_or_gt_of_ne (fun hc : j.val = j'.val => hne (Fin.ext hc)) with hlt | hlt
  · have h1 : tau n j j = ⟨0, j.pos⟩ := by
      rw [tau_apply]; unfold tauF; rw [dif_neg (by omega), if_pos rfl]
    have h2 : tau n j' j = ⟨j.val + 1, by have := j'.isLt; omega⟩ := by
      rw [tau_apply]; unfold tauF; rw [dif_pos hlt]
    rw [h] at h1
    rw [h1] at h2
    exact absurd (congrArg Fin.val h2) (by simp)
  · have h1 : tau n j' j' = ⟨0, j'.pos⟩ := by
      rw [tau_apply]; unfold tauF; rw [dif_neg (by omega), if_pos rfl]
    have h2 : tau n j j' = ⟨j'.val + 1, by have := j.isLt; omega⟩ := by
      rw [tau_apply]; unfold tauF; rw [dif_pos hlt]
    rw [h] at h2
    rw [h1] at h2
    exact absurd (congrArg Fin.val h2) (by simp)

private lemma tau_zero (h : 0 < n) : tau n ⟨0, h⟩ = 1 := by
  ext i
  rw [tau_apply]
  unfold tauF
  rw [dif_neg (by simp)]
  by_cases hi : i = (⟨0, h⟩ : Fin n)
  · rw [if_pos hi]
    subst hi
    rfl
  · rw [if_neg hi]
    rfl

end Tau

section Chain

variable {n : ℕ}

private lemma ttr_card (x z : Equiv.Perm (Fin n)) :
    ((Finset.univ.filter fun j : Fin n => ∀ i : Fin n, z i = topToRandomInsert x j i)
      : Finset (Fin n))
      = Finset.univ.filter fun j : Fin n => z = x * tau n j := by
  apply Finset.filter_congr
  intro j _
  constructor
  · intro h
    refine Equiv.ext (fun i => ?_)
    rw [h i, insert_eq]
    rfl
  · intro h i
    rw [h, insert_eq]
    rfl

private lemma ttr_sum (x : Equiv.Perm (Fin n)) (f : Equiv.Perm (Fin n) → ℝ) :
    ∑ z, topToRandom n x z * f z = (n:ℝ)⁻¹ * ∑ j : Fin n, f (x * tau n j) := by
  classical
  have hterm : ∀ z : Equiv.Perm (Fin n), topToRandom n x z * f z
      = (n:ℝ)⁻¹ * ∑ j : Fin n, (if z = x * tau n j then f z else 0) := by
    intro z
    rw [topToRandom, ttr_card]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
    rw [div_mul_eq_mul_div, mul_comm]
    ring
  rw [Finset.sum_congr rfl (fun z _ => hterm z), ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_ite_eq' Finset.univ (x * tau n j) f]
  rw [if_pos (Finset.mem_univ _)]

private lemma ttr_nonneg (x z : Equiv.Perm (Fin n)) : 0 ≤ topToRandom n x z := by
  rw [topToRandom]
  positivity

private lemma ttr_stochastic (hn : 0 < n) : IsStochastic (topToRandom n) := by
  refine ⟨ttr_nonneg, fun x => ?_⟩
  have h := ttr_sum x (fun _ => (1:ℝ))
  simp only [mul_one] at h
  rw [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (by omega))

private lemma ttr_col_sum (hn : 0 < n) (y : Equiv.Perm (Fin n)) :
    ∑ x, topToRandom n x y = 1 := by
  classical
  have hterm : ∀ x : Equiv.Perm (Fin n), topToRandom n x y
      = (n:ℝ)⁻¹ * ∑ j : Fin n, (if y = x * tau n j then (1:ℝ) else 0) := by
    intro x
    rw [topToRandom, ttr_card]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
      mul_one]
    rw [div_eq_inv_mul]
  rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum, Finset.sum_comm]
  have hinner : ∀ j : Fin n,
      ∑ x : Equiv.Perm (Fin n), (if y = x * tau n j then (1:ℝ) else 0) = 1 := by
    intro j
    have : ∀ x : Equiv.Perm (Fin n),
        (if y = x * tau n j then (1:ℝ) else 0)
          = (if x = y * (tau n j)⁻¹ then (1:ℝ) else 0) := by
      intro x
      by_cases h : y = x * tau n j
      · rw [if_pos h, if_pos (by rw [h, mul_inv_cancel_right])]
      · rw [if_neg h, if_neg (by intro hc; exact h (by rw [hc, inv_mul_cancel_right]))]
    rw [Finset.sum_congr rfl (fun x _ => this x),
      Finset.sum_ite_eq' Finset.univ (y * (tau n j)⁻¹) (fun _ => (1:ℝ)),
      if_pos (Finset.mem_univ _)]
  rw [Finset.sum_congr rfl (fun j _ => hinner j), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (by omega))

private lemma ttr_stationary (hn : 0 < n) :
    IsStationary (topToRandom n) (uniformDist (Equiv.Perm (Fin n))) := by
  constructor
  · constructor
    · intro x
      simp only [uniformDist]
      positivity
    · simp only [uniformDist]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      refine mul_inv_cancel₀ ?_
      exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  · funext y
    rw [Matrix.vecMul]
    show ∑ x, uniformDist (Equiv.Perm (Fin n)) x * topToRandom n x y
      = uniformDist (Equiv.Perm (Fin n)) y
    simp only [uniformDist]
    rw [← Finset.mul_sum, ttr_col_sum hn y, mul_one]

end Chain

section Irred

variable {n : ℕ}

private lemma ttr_transl (a x y : Equiv.Perm (Fin n)) :
    topToRandom n (a * x) (a * y) = topToRandom n x y := by
  classical
  have hset : (Finset.univ.filter fun j : Fin n => a * y = a * x * tau n j)
      = (Finset.univ.filter fun j : Fin n => y = x * tau n j) := by
    apply Finset.filter_congr
    intro j _
    constructor
    · intro h
      exact mul_left_cancel (by rw [h, mul_assoc])
    · intro h
      rw [h, mul_assoc]
  rw [topToRandom, topToRandom, ttr_card, ttr_card, hset]

private lemma ttr_pow_nonneg (t : ℕ) (x y : Equiv.Perm (Fin n)) :
    0 ≤ ((topToRandom n) ^ t) x y := by
  induction t generalizing x y with
  | zero =>
      rw [pow_zero, Matrix.one_apply]
      split_ifs <;> norm_num
  | succ t ih =>
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg (fun z _ => mul_nonneg (ih x z) (ttr_nonneg z y))

private lemma ttr_pow_transl (t : ℕ) (a x y : Equiv.Perm (Fin n)) :
    ((topToRandom n) ^ t) (a * x) (a * y) = ((topToRandom n) ^ t) x y := by
  induction t generalizing x y with
  | zero =>
      rw [pow_zero, Matrix.one_apply, Matrix.one_apply]
      by_cases h : x = y
      · rw [if_pos h, if_pos (by rw [h])]
      · rw [if_neg h, if_neg (fun hc => h (mul_left_cancel hc))]
  | succ t ih =>
      simp only [pow_succ, Matrix.mul_apply]
      refine (Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun w => ?_)).symm
      show ((topToRandom n) ^ t) x w * topToRandom n w y
        = ((topToRandom n) ^ t) (a * x) (a * w) * topToRandom n (a * w) (a * y)
      rw [ih, ttr_transl]

private lemma ttr_pow_add_pos {s t : ℕ} {x z y : Equiv.Perm (Fin n)}
    (h1 : 0 < ((topToRandom n) ^ s) x z) (h2 : 0 < ((topToRandom n) ^ t) z y) :
    0 < ((topToRandom n) ^ (s + t)) x y := by
  rw [pow_add, Matrix.mul_apply]
  refine Finset.sum_pos' (fun w _ => mul_nonneg (ttr_pow_nonneg s x w) (ttr_pow_nonneg t w y))
    ⟨z, Finset.mem_univ z, mul_pos h1 h2⟩

private lemma ttr_gen_pos (hn : 0 < n) (j : Fin n) (x : Equiv.Perm (Fin n)) :
    0 < topToRandom n x (x * tau n j) := by
  classical
  rw [topToRandom, ttr_card]
  have hj : j ∈ Finset.univ.filter fun k : Fin n => x * tau n j = x * tau n k :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hcard : 0 < (Finset.univ.filter fun k : Fin n => x * tau n j = x * tau n k).card :=
    Finset.card_pos.mpr ⟨j, hj⟩
  have h1 : (0:ℝ) < ((Finset.univ.filter fun k : Fin n =>
      x * tau n j = x * tau n k).card : ℝ) := by exact_mod_cast hcard
  have h2 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  positivity

private lemma inv_mem_mclosure {G : Type*} [Group G] [Fintype G] (S : Set G) {g : G}
    (hg : g ∈ Submonoid.closure S) : g⁻¹ ∈ Submonoid.closure S := by
  have hord : 0 < orderOf g := orderOf_pos g
  have hmul : g ^ (orderOf g - 1) * g = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hord]
    exact pow_orderOf_eq_one g
  rw [inv_eq_of_mul_eq_one_left hmul]
  exact Submonoid.pow_mem _ hg _

private lemma tau_val (j i : Fin n) :
    ((tau n j i : Fin n) : ℕ)
      = if (i:ℕ) < (j:ℕ) then (i:ℕ) + 1 else if (i:ℕ) = (j:ℕ) then 0 else (i:ℕ) := by
  rw [tau_apply]
  simp only [tauF]
  by_cases h1 : (i:ℕ) < (j:ℕ)
  · rw [dif_pos h1, if_pos h1]
  · rw [dif_neg h1, if_neg h1]
    by_cases h2 : i = j
    · rw [if_pos h2, if_pos (congrArg Fin.val h2)]
    · rw [if_neg h2, if_neg (fun hc => h2 (Fin.ext hc))]

private lemma tau_last (m : ℕ) :
    tau (m + 2) ⟨m + 1, by omega⟩ = finRotate (m + 2) := by
  refine Equiv.ext (fun i => Fin.ext ?_)
  rw [tau_val, finRotate_apply]
  have hv : ((i + 1 : Fin (m+2)) : ℕ) = ((i:ℕ) + 1) % (m + 2) := by
    simp [Fin.add_def]
  have hlt := i.isLt
  rw [hv]
  show (if (i:ℕ) < m + 1 then (i:ℕ) + 1 else if (i:ℕ) = m + 1 then 0 else (i:ℕ))
      = ((i:ℕ) + 1) % (m + 2)
  by_cases h1 : (i:ℕ) < m + 1
  · rw [if_pos h1, Nat.mod_eq_of_lt (by omega)]
  · have hi : (i:ℕ) = m + 1 := by omega
    rw [if_neg h1, if_pos hi, hi]
    simp

private lemma tau_one (m : ℕ) :
    tau (m + 2) (1 : Fin (m + 2)) = Equiv.swap (0 : Fin (m+2)) (1 : Fin (m+2)) := by
  have hv1 : ((1 : Fin (m+2)) : ℕ) = 1 := rfl
  have hv0 : ((0 : Fin (m+2)) : ℕ) = 0 := rfl
  refine Equiv.ext (fun i => Fin.ext ?_)
  rw [tau_val, hv1, Equiv.swap_apply_def]
  by_cases h1 : i = (0 : Fin (m+2))
  · subst h1
    rw [hv0, if_pos (by norm_num), if_pos rfl, hv1]
  · by_cases h2 : i = (1 : Fin (m+2))
    · subst h2
      rw [hv1, if_neg (by norm_num), if_pos rfl, if_neg h1, if_pos rfl, hv0]
    · have hne0 : (i:ℕ) ≠ 0 := fun hc => h1 (Fin.ext (by rw [hc, hv0]))
      have hne1 : (i:ℕ) ≠ 1 := fun hc => h2 (Fin.ext (by rw [hc, hv1]))
      rw [if_neg (by omega), if_neg hne1, if_neg h1, if_neg h2]

private lemma tau_closure (m : ℕ) :
    Submonoid.closure (Set.range (tau (m + 2))) = ⊤ := by
  classical
  set M := Submonoid.closure (Set.range (tau (m + 2))) with hM
  let H : Subgroup (Equiv.Perm (Fin (m+2))) :=
    { M with inv_mem' := fun {g} hg => inv_mem_mclosure _ hg }
  have hHM : ∀ g, g ∈ H ↔ g ∈ M := fun g => Iff.rfl
  have hc : (finRotate (m+2)) ∈ H := by
    rw [hHM, hM, ← tau_last m]
    exact Submonoid.subset_closure ⟨_, rfl⟩
  have hrot0 : (finRotate (m+2)) (0 : Fin (m+2)) = (1 : Fin (m+2)) := by
    rw [finRotate_apply, zero_add]
  have hs : Equiv.swap (0 : Fin (m+2)) ((finRotate (m+2)) (0 : Fin (m+2))) ∈ H := by
    rw [hHM, hM, hrot0, ← tau_one m]
    exact Submonoid.subset_closure ⟨_, rfl⟩
  have htop := _root_.Equiv.Perm.closure_cycle_adjacent_swap
    (isCycle_finRotate (n := m)) (support_finRotate (n := m)) (0 : Fin (m+2))
  have hle : (⊤ : Subgroup (Equiv.Perm (Fin (m+2)))) ≤ H := by
    rw [← htop]
    refine (Subgroup.closure_le H).mpr ?_
    rintro g (rfl | rfl)
    · exact hc
    · exact hs
  refine le_antisymm le_top (fun g _ => ?_)
  exact (hHM g).mp (hle (Subgroup.mem_top g))

private lemma ttr_irred (m : ℕ) : Irreducible (topToRandom (m + 2)) := by
  have hn : 0 < m + 2 := by omega
  have key : ∀ g : Equiv.Perm (Fin (m+2)),
      ∃ t : ℕ, 0 < ((topToRandom (m+2)) ^ t) 1 g := by
    intro g
    have hmem : g ∈ Submonoid.closure (Set.range (tau (m+2))) := by
      rw [tau_closure m]; exact Submonoid.mem_top g
    refine Submonoid.closure_induction ?_ ?_ ?_ hmem
    · rintro x ⟨j, rfl⟩
      refine ⟨1, ?_⟩
      rw [pow_one]
      have := ttr_gen_pos hn j (1 : Equiv.Perm (Fin (m+2)))
      rwa [one_mul] at this
    · exact ⟨0, by rw [pow_zero, Matrix.one_apply_eq]; norm_num⟩
    · rintro a b - - ⟨t₁, h₁⟩ ⟨t₂, h₂⟩
      refine ⟨t₁ + t₂, ?_⟩
      have h₂' : 0 < ((topToRandom (m+2)) ^ t₂) a (a * b) := by
        have h := ttr_pow_transl t₂ a 1 b
        rw [mul_one] at h
        rw [h]
        exact h₂
      exact ttr_pow_add_pos h₁ h₂'
  intro x y
  obtain ⟨t, ht⟩ := key (x⁻¹ * y)
  refine ⟨t, ?_⟩
  have h := ttr_pow_transl t x 1 (x⁻¹ * y)
  rw [mul_one, mul_inv_cancel_left] at h
  rw [h]
  exact ht

end Irred

/-! ### The death chain and the coupon-collector count -/

section Death

/-- `dcnt n m p`: the number of length-`m` insertion sequences after which the
tracked card, starting at position `p`, has never been at the top. -/
private def dcnt (n : ℕ) : ℕ → ℕ → ℕ
  | 0, p => if p = 0 then 0 else 1
  | (m + 1), p => if p = 0 then 0 else p * dcnt n m p + (n - p) * dcnt n m (p - 1)

/-- `hpoly p d M` is the complete homogeneous symmetric polynomial
`h_M(p, p-1, …, p-d)`, defined by peeling off the smallest variable. -/
private def hpoly (p : ℕ) : ℕ → ℕ → ℕ
  | 0, M => p ^ M
  | (d + 1), M => ∑ a ∈ Finset.range (M + 1), (p - (d + 1)) ^ a * hpoly p d (M - a)

private lemma hpoly_zero (p d : ℕ) : hpoly p d 0 = 1 := by
  induction d with
  | zero => rw [hpoly, pow_zero]
  | succ d ih => rw [hpoly, Finset.sum_range_one, pow_zero, one_mul, Nat.sub_zero, ih]

/-- The geometric identity `k · ∑_{a≤M} x^a y^{M-a} + x^{M+1} = y^{M+1}` when
`y = x + k`. -/
private lemma geom_id (x k M : ℕ) :
    k * (∑ a ∈ Finset.range (M + 1), x ^ a * (x + k) ^ (M - a)) + x ^ (M + 1)
      = (x + k) ^ (M + 1) := by
  induction M with
  | zero =>
      rw [Finset.sum_range_one]
      simp only [pow_zero, Nat.sub_self, one_mul, mul_one, zero_add, pow_one]
      omega
  | succ M ih =>
      have hsplit : (∑ a ∈ Finset.range (M + 2), x ^ a * (x + k) ^ (M + 1 - a))
          = (x + k) * (∑ a ∈ Finset.range (M + 1), x ^ a * (x + k) ^ (M - a))
            + x ^ (M + 1) := by
        rw [Finset.sum_range_succ, Finset.mul_sum]
        congr 1
        · refine Finset.sum_congr rfl (fun a ha => ?_)
          rw [Finset.mem_range] at ha
          rw [← mul_assoc, mul_comm (x + k) (x ^ a), mul_assoc]
          congr 1
          rw [← pow_succ']
          congr 1
          omega
        · rw [Nat.sub_self, pow_zero, mul_one]
      rw [hsplit]
      have : k * ((x + k) * (∑ a ∈ Finset.range (M + 1), x ^ a * (x + k) ^ (M - a))
          + x ^ (M + 1)) + x ^ (M + 2)
          = (x + k) * (k * (∑ a ∈ Finset.range (M + 1), x ^ a * (x + k) ^ (M - a))
            + x ^ (M + 1)) := by
        ring
      rw [this, ih]
      rw [← pow_succ']

private lemma hpoly_bound : ∀ (d p M : ℕ), d ≤ p →
    Nat.factorial d * hpoly p d M ≤ p ^ (M + d) := by
  intro d
  induction d with
  | zero => intro p M _; rw [hpoly, Nat.factorial_zero, one_mul, Nat.add_zero]
  | succ d ih =>
      intro p M hdp
      have hd : d ≤ p := by omega
      rw [hpoly]
      have hx : p - (d + 1) + (d + 1) = p := by omega
      have hstep : ∀ a ∈ Finset.range (M + 1),
          Nat.factorial (d + 1) * ((p - (d+1)) ^ a * hpoly p d (M - a))
            ≤ (d + 1) * ((p - (d+1)) ^ a * p ^ (M - a + d)) := by
        intro a _
        rw [Nat.factorial_succ]
        calc (d + 1) * Nat.factorial d * ((p - (d+1)) ^ a * hpoly p d (M - a))
            = (d + 1) * ((p - (d+1)) ^ a * (Nat.factorial d * hpoly p d (M - a))) := by ring
          _ ≤ (d + 1) * ((p - (d+1)) ^ a * p ^ (M - a + d)) := by
              exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (ih p (M - a) hd))
      rw [Finset.mul_sum]
      refine le_trans (Finset.sum_le_sum hstep) ?_
      have hfac : ∀ a ∈ Finset.range (M + 1),
          (d + 1) * ((p - (d+1)) ^ a * p ^ (M - a + d))
            = p ^ d * ((d + 1) * ((p - (d+1)) ^ a * p ^ (M - a))) := by
        intro a ha
        rw [Finset.mem_range] at ha
        rw [pow_add]
        ring
      rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum, ← Finset.mul_sum]
      have hgeo := geom_id (p - (d+1)) (d + 1) M
      rw [hx] at hgeo
      have hle : (d + 1) * (∑ a ∈ Finset.range (M + 1), (p - (d+1)) ^ a * p ^ (M - a))
          ≤ p ^ (M + 1) := by omega
      calc p ^ d * ((d + 1) * ∑ a ∈ Finset.range (M + 1), (p - (d+1)) ^ a * p ^ (M - a))
          ≤ p ^ d * p ^ (M + 1) := Nat.mul_le_mul_left _ hle
        _ = p ^ (M + (d + 1)) := by rw [← pow_add]; congr 1; omega

private lemma hpoly_rec : ∀ (d p M : ℕ),
    hpoly p (d + 1) (M + 1) = p * hpoly p (d + 1) M + hpoly (p - 1) d (M + 1) := by
  intro d
  induction d with
  | zero =>
      intro p M
      rw [hpoly, hpoly, hpoly, Finset.sum_range_succ]
      have hterm : ∀ a ∈ Finset.range (M + 1),
          (p - 1) ^ a * hpoly p 0 (M + 1 - a) = p * ((p - 1) ^ a * hpoly p 0 (M - a)) := by
        intro a ha
        rw [Finset.mem_range] at ha
        rw [hpoly, hpoly]
        have : M + 1 - a = (M - a) + 1 := by omega
        rw [this, pow_succ]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      congr 1
      rw [Nat.sub_self, hpoly, pow_zero, mul_one]
  | succ d ih =>
      intro p M
      have hsub : p - 1 - (d + 1) = p - (d + 1 + 1) := by omega
      rw [hpoly, hpoly, hpoly, hsub]
      rw [Finset.sum_range_succ (fun a => (p - (d + 1 + 1)) ^ a * hpoly p (d+1) (M + 1 - a)) (M+1)]
      have hterm : ∀ a ∈ Finset.range (M + 1),
          (p - (d + 1 + 1)) ^ a * hpoly p (d+1) (M + 1 - a)
            = p * ((p - (d + 1 + 1)) ^ a * hpoly p (d+1) (M - a))
              + (p - (d + 1 + 1)) ^ a * hpoly (p-1) d (M + 1 - a) := by
        intro a ha
        rw [Finset.mem_range] at ha
        have hMa : M + 1 - a = (M - a) + 1 := by omega
        rw [hMa, ih p (M - a), ← hMa]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [Finset.sum_range_succ (fun a => (p - (d + 1 + 1)) ^ a * hpoly (p-1) d (M + 1 - a)) (M+1)]
      simp only [Nat.sub_self, hpoly_zero, mul_one]
      ring

private def Cf (n p d : ℕ) : ℕ := ∏ k ∈ Finset.range d, (n - p + k)

private lemma Cf_zero (n p : ℕ) : Cf n p 0 = 1 := by rw [Cf, Finset.prod_range_zero]

private lemma Cf_succ (n q d : ℕ) (h : q + 1 ≤ n) :
    Cf n (q + 1) (d + 1) = (n - (q + 1)) * Cf n q d := by
  rw [Cf, Cf, Finset.prod_range_succ']
  have hterm : ∀ i ∈ Finset.range d, n - (q + 1) + (i + 1) = n - q + i := by
    intro i _; omega
  rw [Finset.prod_congr rfl hterm, Nat.add_zero]
  ring

private lemma Cf_top (n d : ℕ) (h : 1 ≤ n) : Cf n (n - 1) d = Nat.factorial d := by
  rw [Cf]
  have hterm : ∀ k ∈ Finset.range d, n - (n - 1) + k = k + 1 := by
    intro k _; omega
  rw [Finset.prod_congr rfl hterm, Finset.prod_range_add_one_eq_factorial]

private def Bd (n p m : ℕ) : ℕ :=
  ∑ d ∈ Finset.range p, (if d ≤ m then Cf n p d * hpoly p d (m - d) else 0)

private lemma Bd_rec (n q m : ℕ) (h : q + 1 ≤ n) :
    Bd n (q + 1) (m + 1) = (q + 1) * Bd n (q + 1) m + (n - (q + 1)) * Bd n q m := by
  set Tf : ℕ → ℕ := fun d =>
    (if d ≤ m + 1 then Cf n (q+1) d * hpoly (q+1) d (m + 1 - d) else 0) with hT
  set Sf : ℕ → ℕ := fun d =>
    (if d ≤ m then Cf n (q+1) d * hpoly (q+1) d (m - d) else 0) with hS
  set Uf : ℕ → ℕ := fun d =>
    (if d ≤ m then Cf n q d * hpoly q d (m - d) else 0) with hU
  have key0 : Tf 0 = (q + 1) * Sf 0 := by
    rw [hT, hS]
    simp only [Nat.zero_le, if_pos, Nat.sub_zero, Cf_zero, one_mul, hpoly]
    rw [pow_succ]
    ring
  have key : ∀ d ∈ Finset.range q, Tf (d + 1) = (q + 1) * Sf (d + 1) + (n - (q+1)) * Uf d := by
    intro d _
    rw [hT, hS, hU]
    by_cases hdm : d < m
    · have e1 : d + 1 ≤ m + 1 := by omega
      have e2 : d + 1 ≤ m := by omega
      have e3 : d ≤ m := by omega
      simp only [if_pos e1, if_pos e2, if_pos e3]
      have hM : m + 1 - (d + 1) = (m - (d+1)) + 1 := by omega
      have hM2 : m - d = (m - (d+1)) + 1 := by omega
      rw [hM, hpoly_rec d (q+1) (m - (d+1))]
      rw [Cf_succ n q d h, hM2]
      simp only [Nat.add_sub_cancel]
      ring
    · by_cases hdm2 : d = m
      · subst hdm2
        have e1 : d + 1 ≤ d + 1 := le_refl _
        have e2 : ¬ (d + 1 ≤ d) := by omega
        have e3 : d ≤ d := le_refl _
        simp only [if_pos e1, if_neg e2, if_pos e3, Nat.sub_self, hpoly_zero,
          mul_one, mul_zero, zero_add]
        exact Cf_succ n q d h
      · have e1 : ¬ (d + 1 ≤ m + 1) := by omega
        have e2 : ¬ (d + 1 ≤ m) := by omega
        have e3 : ¬ (d ≤ m) := by omega
        simp only [if_neg e1, if_neg e2, if_neg e3, mul_zero, Nat.add_zero]
  have hL : Bd n (q+1) (m+1) = (∑ d ∈ Finset.range q, Tf (d + 1)) + Tf 0 := by
    rw [Bd]
    exact Finset.sum_range_succ' Tf q
  have hR1 : Bd n (q+1) m = (∑ d ∈ Finset.range q, Sf (d + 1)) + Sf 0 := by
    rw [Bd]
    exact Finset.sum_range_succ' Sf q
  have hR2 : Bd n q m = ∑ d ∈ Finset.range q, Uf d := rfl
  rw [hL, hR1, hR2, Finset.sum_congr rfl key, key0, Finset.sum_add_distrib,
    mul_add, Finset.mul_sum, Finset.mul_sum]
  ring

private lemma dcnt_le_Bd (n : ℕ) : ∀ (m p : ℕ), p ≤ n → dcnt n m p ≤ Bd n p m := by
  intro m
  induction m with
  | zero =>
      intro p _
      rw [dcnt]
      by_cases hp : p = 0
      · rw [if_pos hp, hp, Bd, Finset.range_zero, Finset.sum_empty]
      · rw [if_neg hp]
        obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
        rw [Bd, Finset.sum_range_succ' _ q]
        simp only [Nat.zero_le, if_pos, Nat.sub_zero, Cf_zero, one_mul, hpoly_zero]
        omega
  | succ m ih =>
      intro p hp
      rw [dcnt]
      by_cases hp0 : p = 0
      · rw [if_pos hp0]
        exact Nat.zero_le _
      · rw [if_neg hp0]
        obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
        rw [Bd_rec n q m hp]
        simp only [Nat.add_sub_cancel]
        exact Nat.add_le_add (Nat.mul_le_mul_left _ (ih (q+1) hp))
          (Nat.mul_le_mul_left _ (ih q (by omega)))

private lemma dcnt_top_bound (n m : ℕ) (hn : 1 ≤ n) :
    dcnt n m (n - 1) ≤ (n - 1) ^ (m + 1) := by
  refine le_trans (dcnt_le_Bd n m (n-1) (by omega)) ?_
  have hterm : ∀ d ∈ Finset.range (n - 1),
      (if d ≤ m then Cf n (n-1) d * hpoly (n-1) d (m - d) else 0) ≤ (n - 1) ^ m := by
    intro d hd
    rw [Finset.mem_range] at hd
    by_cases hdm : d ≤ m
    · rw [if_pos hdm, Cf_top n d hn]
      have := hpoly_bound d (n-1) (m - d) (by omega)
      calc Nat.factorial d * hpoly (n-1) d (m - d) ≤ (n-1) ^ ((m - d) + d) := this
        _ = (n-1) ^ m := by congr 1; omega
    · rw [if_neg hdm]
      exact Nat.zero_le _
  calc Bd n (n-1) m ≤ ∑ _d ∈ Finset.range (n - 1), (n - 1) ^ m :=
        Finset.sum_le_sum hterm
    _ = (n - 1) * (n - 1) ^ m := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ = (n - 1) ^ (m + 1) := by rw [pow_succ]; ring

end Death

/-! ### Path sums -/

section PathSums

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma pathWeight_snoc (P : Matrix V V ℝ) (m : ℕ) (p : Fin (m+1) → V) (v : V) :
    pathWeight P (Fin.snoc p v : Fin (m+2) → V)
      = pathWeight P p * P (p (Fin.last m)) v := by
  rw [pathWeight, pathWeight, Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [Fin.snoc_castSucc, Fin.succ_castSucc]
  · rw [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]

private lemma pathWeight_cons (P : Matrix V V ℝ) (m : ℕ) (u : V) (p : Fin (m+1) → V) :
    pathWeight P (Fin.cons u p : Fin (m+2) → V)
      = P u (p 0) * pathWeight P p := by
  rw [pathWeight, pathWeight, Fin.prod_univ_succ]
  have hfst : (Fin.cons u p : Fin (m+2) → V) ((0 : Fin (m+1)).castSucc) = u := by simp
  have hsnd : (Fin.cons u p : Fin (m+2) → V) ((0 : Fin (m+1)).succ) = p 0 := by simp
  have hrest : ∀ i : Fin m,
      P ((Fin.cons u p : Fin (m+2) → V) ((i.succ : Fin (m+1)).castSucc))
        ((Fin.cons u p : Fin (m+2) → V) ((i.succ : Fin (m+1)).succ))
      = P (p i.castSucc) (p i.succ) := by
    intro i
    have e : (i.succ : Fin (m+1)).castSucc = (i.castSucc : Fin (m+1)).succ :=
      (Fin.succ_castSucc i).symm
    rw [e, Fin.cons_succ, Fin.cons_succ]
  rw [hfst, hsnd, Finset.prod_congr rfl (fun i _ => hrest i)]

private lemma marg (P : Matrix V V ℝ) (hP : IsStochastic P) (m : ℕ)
    (g : (Fin (m+1) → V) → ℝ) :
    ∑ ω : Fin (m+2) → V, pathWeight P ω * g (Fin.init ω)
      = ∑ ω : Fin (m+1) → V, pathWeight P ω * g ω := by
  classical
  have hEq := Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (m+2) => V))
    (fun q : V × (Fin (m+1) → V) => pathWeight P (Fin.snoc q.2 q.1 : Fin (m+2) → V)
      * g (Fin.init (Fin.snoc q.2 q.1 : Fin (m+2) → V)))
    (fun ω : Fin (m+2) → V => pathWeight P ω * g (Fin.init ω))
    (fun q => rfl)
  rw [← hEq, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hterm : ∀ v : V, pathWeight P (Fin.snoc p v : Fin (m+2) → V)
      * g (Fin.init (Fin.snoc p v : Fin (m+2) → V))
      = (pathWeight P p * g p) * P (p (Fin.last m)) v := by
    intro v
    rw [pathWeight_snoc, Fin.init_snoc]
    ring
  rw [Finset.sum_congr rfl (fun v _ => hterm v), ← Finset.mul_sum, hP.2, mul_one]

/-- Survival through all of times `0, …, m`. -/
private def survPath (P : Matrix V V ℝ) (x : V) (ind : V → ℝ) (m : ℕ) : ℝ :=
  ∑ ω : Fin (m+1) → V, (if ω 0 = x then pathWeight P ω else 0) * ∏ w : Fin (m+1), ind (ω w)

/-- Survival through times `0, …, m-1` along a path of length `m+1`. -/
private def survPath' (P : Matrix V V ℝ) (x : V) (ind : V → ℝ) (m : ℕ) : ℝ :=
  ∑ ω : Fin (m+1) → V,
    (if ω 0 = x then pathWeight P ω else 0) * ∏ w : Fin m, ind (ω w.castSucc)

private lemma sum_fin_one (f : V → ℝ) (x : V) :
    ∑ ω : Fin 1 → V, (if ω 0 = x then f (ω 0) else 0) = f x := by
  classical
  have hE := Fintype.sum_equiv (Equiv.funUnique (Fin 1) V).symm
    (fun v : V => if v = x then f v else 0)
    (fun ω : Fin 1 → V => if ω 0 = x then f (ω 0) else 0)
    (fun v => rfl)
  rw [← hE, Finset.sum_ite_eq' Finset.univ x f, if_pos (Finset.mem_univ _)]

private lemma survPath'_zero (P : Matrix V V ℝ) (x : V) (ind : V → ℝ) :
    survPath' P x ind 0 = 1 := by
  classical
  rw [survPath']
  have hterm : ∀ ω : Fin 1 → V,
      (if ω 0 = x then pathWeight P ω else 0) * ∏ w : Fin 0, ind (ω w.castSucc)
        = if ω 0 = x then (1:ℝ) else 0 := by
    intro ω
    rw [pathWeight]
    simp
  rw [Finset.sum_congr rfl (fun ω _ => hterm ω)]
  exact sum_fin_one (fun _ => (1:ℝ)) x

private lemma survPath_zero (P : Matrix V V ℝ) (x : V) (ind : V → ℝ) :
    survPath P x ind 0 = ind x := by
  classical
  rw [survPath]
  have hterm : ∀ ω : Fin 1 → V,
      (if ω 0 = x then pathWeight P ω else 0) * ∏ w : Fin 1, ind (ω w)
        = if ω 0 = x then ind (ω 0) else 0 := by
    intro ω
    rw [pathWeight, Fin.prod_univ_one]
    simp
  rw [Finset.sum_congr rfl (fun ω _ => hterm ω)]
  exact sum_fin_one ind x

private lemma survPath'_succ (P : Matrix V V ℝ) (hP : IsStochastic P) (x : V)
    (ind : V → ℝ) (m : ℕ) :
    survPath' P x ind (m + 1) = survPath P x ind m := by
  classical
  rw [survPath', survPath]
  have hterm : ∀ ω : Fin (m+2) → V,
      (if ω 0 = x then pathWeight P ω else 0) * ∏ w : Fin (m+1), ind (ω w.castSucc)
        = pathWeight P ω * ((if Fin.init ω 0 = x then (1:ℝ) else 0)
            * ∏ w : Fin (m+1), ind (Fin.init ω w)) := by
    intro ω
    have h0 : Fin.init ω 0 = ω 0 := rfl
    have h1 : ∀ w : Fin (m+1), Fin.init ω w = ω w.castSucc := fun w => rfl
    rw [h0, Finset.prod_congr rfl (fun w _ => congrArg ind (h1 w))]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun ω _ => hterm ω)]
  rw [marg P hP m (fun ω => (if ω 0 = x then (1:ℝ) else 0) * ∏ w : Fin (m+1), ind (ω w))]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  split_ifs <;> ring

private lemma survPath_succ (P : Matrix V V ℝ) (x : V) (ind : V → ℝ) (m : ℕ) :
    survPath P x ind (m + 1) = ind x * ∑ z, P x z * survPath P z ind m := by
  classical
  rw [survPath]
  have hE := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m+2) => V))
    (fun q : V × (Fin (m+1) → V) =>
      (if (Fin.cons q.1 q.2 : Fin (m+2) → V) 0 = x then
        pathWeight P (Fin.cons q.1 q.2 : Fin (m+2) → V) else 0)
        * ∏ w : Fin (m+2), ind ((Fin.cons q.1 q.2 : Fin (m+2) → V) w))
    (fun ω : Fin (m+2) → V =>
      (if ω 0 = x then pathWeight P ω else 0) * ∏ w : Fin (m+2), ind (ω w))
    (fun q => rfl)
  rw [← hE, Fintype.sum_prod_type]
  have hterm : ∀ (u : V) (p : Fin (m+1) → V),
      (if (Fin.cons u p : Fin (m+2) → V) 0 = x then
        pathWeight P (Fin.cons u p : Fin (m+2) → V) else 0)
        * ∏ w : Fin (m+2), ind ((Fin.cons u p : Fin (m+2) → V) w)
      = (if u = x then (1:ℝ) else 0) * ind u *
          (P u (p 0) * (pathWeight P p * ∏ w : Fin (m+1), ind (p w))) := by
    intro u p
    rw [pathWeight_cons, Fin.prod_univ_succ, Fin.cons_zero]
    have h1 : ∀ w : Fin (m+1), (Fin.cons u p : Fin (m+2) → V) w.succ = p w := by
      intro w; rw [Fin.cons_succ]
    rw [Finset.prod_congr rfl (fun w _ => congrArg ind (h1 w))]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun u _ =>
    Finset.sum_congr rfl (fun p _ => hterm u p))]
  have hcollapse : ∀ u : V,
      ∑ p : Fin (m+1) → V, (if u = x then (1:ℝ) else 0) * ind u *
          (P u (p 0) * (pathWeight P p * ∏ w : Fin (m+1), ind (p w)))
        = (if u = x then ind x * ∑ z, P x z * survPath P z ind m else 0) := by
    intro u
    rw [← Finset.mul_sum]
    have hin : ∑ p : Fin (m+1) → V,
        P u (p 0) * (pathWeight P p * ∏ w : Fin (m+1), ind (p w))
          = ∑ z, P u z * survPath P z ind m := by
      have hstep : ∀ p : Fin (m+1) → V,
          P u (p 0) * (pathWeight P p * ∏ w : Fin (m+1), ind (p w))
            = ∑ z, P u z * ((if p 0 = z then pathWeight P p else 0)
                * ∏ w : Fin (m+1), ind (p w)) := by
        intro p
        have hz : ∀ z : V, P u z * ((if p 0 = z then pathWeight P p else 0)
            * ∏ w : Fin (m+1), ind (p w))
            = if p 0 = z then
                P u z * (pathWeight P p * ∏ w : Fin (m+1), ind (p w)) else 0 := by
          intro z
          by_cases h : p 0 = z
          · rw [if_pos h, if_pos h]
          · rw [if_neg h, if_neg h, zero_mul, mul_zero]
        rw [Finset.sum_congr rfl (fun z _ => hz z),
          Finset.sum_ite_eq Finset.univ (p 0)
            (fun z => P u z * (pathWeight P p * ∏ w : Fin (m+1), ind (p w))),
          if_pos (Finset.mem_univ _)]
      rw [Finset.sum_congr rfl (fun p _ => hstep p), Finset.sum_comm]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [← Finset.mul_sum, survPath]
    rw [hin]
    by_cases h : u = x
    · rw [if_pos h, if_pos h, h]; ring
    · rw [if_neg h, if_neg h]; ring
  rw [Finset.sum_congr rfl (fun u _ => hcollapse u),
    Finset.sum_ite_eq' Finset.univ x (fun _ => ind x * ∑ z, P x z * survPath P z ind m),
    if_pos (Finset.mem_univ _)]

end PathSums

/-! ### The stopping-rule tail equals the survival probability -/

section StopTail

variable {n : ℕ}

private def indb {n : ℕ} (b : Fin n) (y : Equiv.Perm (Fin n)) : ℝ :=
  if y ⟨0, b.pos⟩ = b then 0 else 1

private lemma rule_zero (n : ℕ) (ω : Fin 1 → Equiv.Perm (Fin n)) :
    topToRandomRule n 0 ω = 0 := by
  rw [topToRandomRule, dif_neg (by omega)]

private lemma rule_pos (n u : ℕ) (hn : 0 < n) (hu : 1 ≤ u)
    (ω : Fin (u + 1) → Equiv.Perm (Fin n)) :
    topToRandomRule n u ω
      = if ω ⟨u - 1, by omega⟩ ⟨0, hn⟩ = ω 0 ⟨n - 1, by omega⟩ then 1 else 0 := by
  rw [topToRandomRule, dif_pos ⟨hn, hu⟩]

private lemma sum_over_last {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
    (x : V) (F : (Fin (t + 1) → V) → ℝ) :
    ∑ y : V, ∑ ω : Fin (t + 1) → V,
        (if ω 0 = x ∧ ω (Fin.last t) = y then F ω else 0)
      = ∑ ω : Fin (t + 1) → V, (if ω 0 = x then F ω else 0) := by
  classical
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  by_cases h : ω 0 = x
  · have hterm : ∀ y : V, (if ω 0 = x ∧ ω (Fin.last t) = y then F ω else 0)
        = (if ω (Fin.last t) = y then F ω else 0) := by
      intro y
      by_cases h2 : ω (Fin.last t) = y
      · rw [if_pos ⟨h, h2⟩, if_pos h2]
      · rw [if_neg (fun hc => h2 hc.2), if_neg h2]
    rw [Finset.sum_congr rfl (fun y _ => hterm y),
      Finset.sum_ite_eq Finset.univ (ω (Fin.last t)) (fun _ => F ω),
      if_pos (Finset.mem_univ _), if_pos h]
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun y _ => ?_)
    rw [if_neg (fun hc => h hc.1)]

private lemma stopAt_sum0 (n : ℕ) (x : Equiv.Perm (Fin n)) :
    ∑ y, stopAtProb (topToRandom n) x (topToRandomRule n) 0 y = 0 := by
  refine Finset.sum_eq_zero (fun y _ => ?_)
  rw [stopAtProb]
  refine Finset.sum_eq_zero (fun ω _ => ?_)
  split_ifs with h
  · rw [rule_zero, mul_zero]
  · rfl

private lemma rule_val (n : ℕ) (hn : 0 < n) {u : ℕ} (hu : 1 ≤ u)
    (ω : Fin (u + 1) → Equiv.Perm (Fin n)) (b : Fin n)
    (hb : ω 0 ⟨n - 1, by omega⟩ = b) :
    topToRandomRule n u ω = 1 - indb b (ω ⟨u - 1, by omega⟩) := by
  rw [topToRandomRule, dif_pos ⟨hn, hu⟩, indb]
  have hp : (⟨0, b.pos⟩ : Fin n) = ⟨0, hn⟩ := rfl
  simp only [hp, hb]
  split_ifs with h
  · norm_num
  · norm_num

private lemma stopAt_sum (n : ℕ) (hn : 0 < n) (x : Equiv.Perm (Fin n)) (s : ℕ) :
    ∑ y, stopAtProb (topToRandom n) x (topToRandomRule n) (s + 1) y
      = survPath' (topToRandom n) x (indb (x ⟨n - 1, by omega⟩)) s
        - survPath' (topToRandom n) x (indb (x ⟨n - 1, by omega⟩)) (s + 1) := by
  classical
  have hstep : ∀ ω : Fin (s + 2) → Equiv.Perm (Fin n), ω 0 = x →
      pathWeight (topToRandom n) ω * (∏ v : Fin (s + 1),
          (1 - topToRandomRule n v.val (pathPrefix ω v)))
        * topToRandomRule n (s + 1) ω
      = pathWeight (topToRandom n) ω
          * (∏ k : Fin s, indb (x ⟨n - 1, by omega⟩) (ω k.castSucc.castSucc))
          * (1 - indb (x ⟨n - 1, by omega⟩) (ω (Fin.last s).castSucc)) := by
    intro ω hω
    have hb0 : ω 0 ⟨n - 1, by omega⟩ = x ⟨n - 1, by omega⟩ := by rw [hω]
    have hprod : (∏ v : Fin (s + 1), (1 - topToRandomRule n v.val (pathPrefix ω v)))
        = ∏ k : Fin s, indb (x ⟨n - 1, by omega⟩) (ω k.castSucc.castSucc) := by
      rw [Fin.prod_univ_succ]
      have h0 : topToRandomRule n ((0 : Fin (s+1)) : ℕ) (pathPrefix ω 0) = 0 := by
        rw [topToRandomRule, dif_neg (by simp)]
      rw [h0, sub_zero, one_mul]
      refine Finset.prod_congr rfl (fun k _ => ?_)
      have hpb : (pathPrefix ω (k.succ : Fin (s+1))) 0 ⟨n - 1, by omega⟩
          = x ⟨n - 1, by omega⟩ := hb0
      rw [rule_val n hn (u := ((k.succ : Fin (s+1)) : ℕ))
        (Nat.succ_le_succ (Nat.zero_le _)) (pathPrefix ω k.succ) _ hpb, sub_sub_cancel]
      refine congrArg (indb (x ⟨n - 1, by omega⟩)) ?_
      refine congrArg ω ?_
      exact Fin.ext (by simp)
    have hlast : topToRandomRule n (s + 1) ω
        = 1 - indb (x ⟨n - 1, by omega⟩) (ω (Fin.last s).castSucc) :=
      rule_val n hn (u := s + 1) (by omega) ω _ hb0
    rw [hprod, hlast]
  have h1 : ∑ y, stopAtProb (topToRandom n) x (topToRandomRule n) (s + 1) y
      = ∑ ω : Fin (s + 2) → Equiv.Perm (Fin n),
          (if ω 0 = x then pathWeight (topToRandom n) ω
            * (∏ k : Fin s, indb (x ⟨n - 1, by omega⟩) (ω k.castSucc.castSucc))
            * (1 - indb (x ⟨n - 1, by omega⟩) (ω (Fin.last s).castSucc)) else 0) := by
    rw [show (∑ y, stopAtProb (topToRandom n) x (topToRandomRule n) (s + 1) y)
        = ∑ y, ∑ ω : Fin (s + 2) → Equiv.Perm (Fin n),
            (if ω 0 = x ∧ ω (Fin.last (s+1)) = y then
              pathWeight (topToRandom n) ω * (∏ v : Fin (s+1),
                (1 - topToRandomRule n v.val (pathPrefix ω v)))
                * topToRandomRule n (s+1) ω else 0) from rfl]
    rw [sum_over_last x]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    by_cases h : ω 0 = x
    · rw [if_pos h, if_pos h, hstep ω h]
    · rw [if_neg h, if_neg h]
  rw [h1]
  have hsplit : ∀ ω : Fin (s + 2) → Equiv.Perm (Fin n),
      (if ω 0 = x then pathWeight (topToRandom n) ω
        * (∏ k : Fin s, indb (x ⟨n - 1, by omega⟩) (ω k.castSucc.castSucc))
        * (1 - indb (x ⟨n - 1, by omega⟩) (ω (Fin.last s).castSucc)) else 0)
      = (if ω 0 = x then pathWeight (topToRandom n) ω
          * (∏ k : Fin s, indb (x ⟨n - 1, by omega⟩) (ω k.castSucc.castSucc)) else 0)
        - (if ω 0 = x then pathWeight (topToRandom n) ω
          * (∏ w : Fin (s+1), indb (x ⟨n - 1, by omega⟩) (ω w.castSucc)) else 0) := by
    intro ω
    have hpr : (∏ w : Fin (s+1), indb (x ⟨n - 1, by omega⟩) (ω w.castSucc))
        = (∏ k : Fin s, indb (x ⟨n - 1, by omega⟩) (ω k.castSucc.castSucc))
          * indb (x ⟨n - 1, by omega⟩) (ω (Fin.last s).castSucc) := by
      rw [Fin.prod_univ_castSucc]
    rw [hpr]
    by_cases h : ω 0 = x
    · rw [if_pos h, if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h, if_neg h, sub_zero]
  rw [Finset.sum_congr rfl (fun ω _ => hsplit ω), Finset.sum_sub_distrib]
  congr 1
  · have hg : ∀ ω : Fin (s + 2) → Equiv.Perm (Fin n),
        (if ω 0 = x then pathWeight (topToRandom n) ω
          * (∏ k : Fin s, indb (x ⟨n - 1, by omega⟩) (ω k.castSucc.castSucc)) else 0)
        = pathWeight (topToRandom n) ω * ((if (Fin.init ω) 0 = x then (1:ℝ) else 0)
            * ∏ k : Fin s, indb (x ⟨n - 1, by omega⟩) ((Fin.init ω) k.castSucc)) := by
      intro ω
      have h0 : (Fin.init ω) 0 = ω 0 := rfl
      have hprodeq : (∏ k : Fin s, indb (x ⟨n - 1, by omega⟩) ((Fin.init ω) k.castSucc))
          = ∏ k : Fin s, indb (x ⟨n - 1, by omega⟩) (ω k.castSucc.castSucc) := rfl
      rw [h0, hprodeq]
      by_cases h : ω 0 = x
      · rw [if_pos h, if_pos h]; ring
      · rw [if_neg h, if_neg h]; ring
    rw [Finset.sum_congr rfl (fun ω _ => hg ω),
      marg (topToRandom n) (ttr_stochastic hn) s
        (fun ω' => (if ω' 0 = x then (1:ℝ) else 0)
          * ∏ k : Fin s, indb (x ⟨n - 1, by omega⟩) (ω' k.castSucc))]
    rw [survPath']
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    by_cases h : ω 0 = x
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  · rw [survPath']
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    by_cases h : ω 0 = x
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, zero_mul]

private lemma stopTail_eq (n : ℕ) (hn : 0 < n) (x : Equiv.Perm (Fin n)) (t : ℕ) :
    stopTailProb (topToRandom n) x (topToRandomRule n) t
      = survPath' (topToRandom n) x (indb (x ⟨n - 1, by omega⟩)) t := by
  induction t with
  | zero =>
      rw [stopTailProb, Finset.sum_range_one, stopAt_sum0, sub_zero, survPath'_zero]
  | succ t ih =>
      rw [stopTailProb, Finset.sum_range_succ, stopAt_sum n hn x t]
      rw [stopTailProb] at ih
      linarith [ih]

end StopTail

/-! ### Lumping: the position of the tracked card is a death chain -/

section Lump

private def dsurvR (n m p : ℕ) : ℝ := (dcnt n m p : ℝ) / (n:ℝ) ^ m

private lemma card_fin_lt (n p : ℕ) (hp : p ≤ n) :
    (Finset.univ.filter fun j : Fin n => (j:ℕ) < p).card = p := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hp0 : p = 0 := by omega
    subst hp0
    simp
  · have hcard : (Finset.univ.filter fun j : Fin n => (j:ℕ) < p).card
        = (Finset.range p).card := by
      refine Finset.card_nbij' (fun j => (j:ℕ))
        (fun k => (⟨k % n, Nat.mod_lt k hn⟩ : Fin n)) ?_ ?_ ?_ ?_
      · intro j hj
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hj
        simp only [Finset.coe_range, Set.mem_Iio]
        exact hj
      · intro k hk
        simp only [Finset.coe_range, Set.mem_Iio] at hk
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
        rw [Nat.mod_eq_of_lt (by omega)]
        exact hk
      · intro j _
        exact Fin.ext (Nat.mod_eq_of_lt j.isLt)
      · intro k hk
        simp only [Finset.coe_range, Set.mem_Iio] at hk
        exact Nat.mod_eq_of_lt (by omega)
    rw [hcard, Finset.card_range]

private lemma card_fin_ge (n p : ℕ) (hp : p ≤ n) :
    (Finset.univ.filter fun j : Fin n => p ≤ (j:ℕ)).card = n - p := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun j : Fin n => (j:ℕ) < p)
  rw [card_fin_lt n p hp, Finset.card_univ, Fintype.card_fin] at h
  have h2 : (Finset.univ.filter fun j : Fin n => ¬ ((j:ℕ) < p))
      = (Finset.univ.filter fun j : Fin n => p ≤ (j:ℕ)) := by
    apply Finset.filter_congr
    intro j _
    constructor
    · intro hj; omega
    · intro hj; omega
  rw [h2] at h
  omega

private lemma tau_inv_val {n : ℕ} (j q : Fin n) (hq : 1 ≤ (q:ℕ)) :
    (((tau n j)⁻¹ q : Fin n) : ℕ) = if (q:ℕ) ≤ (j:ℕ) then (q:ℕ) - 1 else (q:ℕ) := by
  have hinv : ((tau n j)⁻¹ : Equiv.Perm (Fin n)) q = tauG n j q := rfl
  rw [hinv]
  simp only [tauG]
  rw [if_neg (by omega)]
  by_cases h : (q:ℕ) ≤ (j:ℕ)
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

private lemma survPath_eq_dsurv (n : ℕ) (hn : 0 < n) (b : Fin n) :
    ∀ (m : ℕ) (y : Equiv.Perm (Fin n)),
      survPath (topToRandom n) y (indb b) m = dsurvR n m ((y.symm b : Fin n) : ℕ) := by
  intro m
  induction m with
  | zero =>
      intro y
      rw [survPath_zero, dsurvR, pow_zero, div_one, dcnt, indb]
      by_cases h : y ⟨0, b.pos⟩ = b
      · have h2 : ((y.symm b : Fin n) : ℕ) = 0 := by
          have : y.symm b = (⟨0, b.pos⟩ : Fin n) := by
            rw [← h]
            exact y.symm_apply_apply _
          rw [this]
        rw [if_pos h, if_pos h2]
        norm_num
      · have h2 : ¬ (((y.symm b : Fin n) : ℕ) = 0) := by
          intro hc
          refine h ?_
          have : y.symm b = (⟨0, b.pos⟩ : Fin n) := Fin.ext hc
          rw [← this, y.apply_symm_apply]
        rw [if_neg h, if_neg h2]
        norm_num
  | succ m ih =>
      intro y
      rw [survPath_succ, ttr_sum]
      have hIH : ∀ j : Fin n, survPath (topToRandom n) (y * tau n j) (indb b) m
          = dsurvR n m ((((y * tau n j).symm b : Fin n)) : ℕ) := fun j => ih _
      rw [Finset.sum_congr rfl (fun j _ => hIH j)]
      set p := ((y.symm b : Fin n) : ℕ) with hp
      have hpn : p < n := (y.symm b).isLt
      by_cases h0 : p = 0
      · have hy : y ⟨0, b.pos⟩ = b := by
          have : y.symm b = (⟨0, b.pos⟩ : Fin n) := Fin.ext h0
          rw [← this, y.apply_symm_apply]
        rw [indb, if_pos hy, dsurvR, dcnt, if_pos h0]
        norm_num
      · have hy : ¬ (y ⟨0, b.pos⟩ = b) := by
          intro hc
          refine h0 ?_
          have : y.symm b = (⟨0, b.pos⟩ : Fin n) := by rw [← hc, y.symm_apply_apply]
          rw [hp, this]
        rw [indb, if_neg hy, one_mul]
        have hval : ∀ j : Fin n, ((((y * tau n j).symm b : Fin n)) : ℕ)
            = if p ≤ (j:ℕ) then p - 1 else p := by
          intro j
          have he : ((y * tau n j).symm b : Fin n) = (tau n j)⁻¹ (y.symm b) := by
            show ((y * tau n j)⁻¹ : Equiv.Perm (Fin n)) b = _
            rw [mul_inv_rev]
            rfl
          rw [he, tau_inv_val j (y.symm b) (by omega)]
        rw [Finset.sum_congr rfl (fun j _ => congrArg (dsurvR n m) (hval j))]
        rw [Finset.sum_congr rfl (fun (j : Fin n) (_ : j ∈ Finset.univ) =>
          apply_ite (dsurvR n m) (p ≤ (j:ℕ)) (p - 1) p)]
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const,
          card_fin_ge n p (le_of_lt hpn), nsmul_eq_mul, nsmul_eq_mul]
        have hcompl : (Finset.univ.filter fun j : Fin n => ¬ (p ≤ (j:ℕ))).card = p := by
          have h2 : (Finset.univ.filter fun j : Fin n => ¬ (p ≤ (j:ℕ)))
              = (Finset.univ.filter fun j : Fin n => (j:ℕ) < p) := by
            apply Finset.filter_congr
            intro j _
            constructor
            · intro hj; omega
            · intro hj; omega
          rw [h2, card_fin_lt n p (le_of_lt hpn)]
        rw [hcompl]
        rw [dsurvR, dsurvR, dsurvR, dcnt, if_neg h0]
        have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
        have hnm : (0:ℝ) < (n:ℝ) ^ m := by positivity
        push_cast
        rw [pow_succ]
        field_simp
        ring

end Lump

/-! ### Assembly -/

section Final

private lemma stopTail_val (n : ℕ) (hn : 0 < n) (x : Equiv.Perm (Fin n)) (s : ℕ) :
    stopTailProb (topToRandom n) x (topToRandomRule n) (s + 1) = dsurvR n s (n - 1) := by
  rw [stopTail_eq n hn x (s + 1), survPath'_succ _ (ttr_stochastic hn),
    survPath_eq_dsurv n hn _ s x]
  congr 1
  rw [Equiv.symm_apply_apply]

private lemma dsurv_bound (n s : ℕ) (hn : 1 ≤ n) :
    dsurvR n s (n - 1) ≤ (n:ℝ) * (((n:ℝ) - 1) / (n:ℝ)) ^ (s + 1) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hnum : (dcnt n s (n - 1) : ℝ) ≤ (((n - 1 : ℕ) : ℝ)) ^ (s + 1) := by
    have := dcnt_top_bound n s hn
    exact_mod_cast this
  have hcast : ((n - 1 : ℕ) : ℝ) = (n:ℝ) - 1 := by
    have : (1:ℕ) ≤ n := hn
    push_cast [Nat.cast_sub this]
    ring
  rw [hcast] at hnum
  have hRHS : (n:ℝ) * (((n:ℝ) - 1) / (n:ℝ)) ^ (s + 1) = ((n:ℝ) - 1) ^ (s + 1) / (n:ℝ) ^ s := by
    rw [div_pow, pow_succ]
    field_simp
    ring
  rw [dsurvR, hRHS]
  gcongr

private lemma numeric_bound (n : ℕ) (hn : 2 ≤ n) (α : ℝ) (t : ℕ)
    (ht : (n:ℝ) * Real.log n + α * n ≤ t) :
    (n:ℝ) * (((n:ℝ) - 1) / (n:ℝ)) ^ t ≤ Real.exp (-α) := by
  have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 : (0:ℝ) < (n:ℝ) := by linarith
  have hA0 : (0:ℝ) ≤ ((n:ℝ) - 1) / (n:ℝ) := by
    apply div_nonneg <;> linarith
  have hA : ((n:ℝ) - 1) / (n:ℝ) ≤ Real.exp (-(1 / (n:ℝ))) := by
    have h := Real.add_one_le_exp (-(1 / (n:ℝ)))
    have he : ((n:ℝ) - 1) / (n:ℝ) = -(1 / (n:ℝ)) + 1 := by field_simp; ring
    rw [he]
    exact h
  have hpow : (((n:ℝ) - 1) / (n:ℝ)) ^ t ≤ (Real.exp (-(1 / (n:ℝ)))) ^ t := by
    gcongr
  have hexp : (Real.exp (-(1 / (n:ℝ)))) ^ t = Real.exp (-((t:ℝ) / (n:ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have hlog : Real.log n - (t:ℝ) / (n:ℝ) ≤ -α := by
    have h1 : Real.log n + α ≤ (t:ℝ) / (n:ℝ) := by
      rw [le_div_iff₀ hn0]
      have hr : (Real.log (n:ℝ) + α) * (n:ℝ) = (n:ℝ) * Real.log n + α * n := by ring
      rw [hr]
      exact ht
    linarith
  calc (n:ℝ) * (((n:ℝ) - 1) / (n:ℝ)) ^ t
      ≤ (n:ℝ) * (Real.exp (-(1 / (n:ℝ)))) ^ t := by
        exact mul_le_mul_of_nonneg_left hpow (le_of_lt hn0)
    _ = Real.exp (Real.log n) * Real.exp (-((t:ℝ) / (n:ℝ))) := by
        rw [hexp, Real.exp_log hn0]
    _ = Real.exp (Real.log n - (t:ℝ) / (n:ℝ)) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-α) := Real.exp_le_exp.mpr hlog

end Final

end

end MarkovMixing

open MarkovMixing

/-- **§6.5.3, Eq. (6.16)** (LPW), the capstone of Chapters 5–6: for the
top-to-random shuffle on `n` cards,
`d(⌈n log n + α n⌉) ≤ e^{-α}` for every `α > 0`. -/
theorem solution (n : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα : 0 < α) :
    distStationary (topToRandom n) (uniformDist (Equiv.Perm (Fin n)))
      ⌈(n : ℝ) * Real.log n + α * n⌉₊ ≤ Real.exp (-α) := by
  obtain ⟨m0, rfl⟩ : ∃ m0, n = m0 + 2 := ⟨n - 2, by omega⟩
  have hn0 : 0 < m0 + 2 := by omega
  have hnR : (2:ℝ) ≤ ((m0 + 2 : ℕ) : ℝ) := by exact_mod_cast hn
  have hpos : 0 < ((m0 + 2 : ℕ) : ℝ) * Real.log ((m0 + 2 : ℕ) : ℝ)
      + α * ((m0 + 2 : ℕ) : ℝ) := by
    have hlog : 0 < Real.log ((m0 + 2 : ℕ) : ℝ) := Real.log_pos (by linarith)
    nlinarith
  set t := ⌈((m0 + 2 : ℕ) : ℝ) * Real.log ((m0 + 2 : ℕ) : ℝ)
    + α * ((m0 + 2 : ℕ) : ℝ)⌉₊ with ht
  have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr (fun hc => by
    have h2 : ((m0 + 2 : ℕ) : ℝ) * Real.log ((m0 + 2 : ℕ) : ℝ)
        + α * ((m0 + 2 : ℕ) : ℝ) ≤ 0 := by
      have := Nat.ceil_eq_zero.mp (ht ▸ hc)
      exact this
    linarith)
  obtain ⟨s, hs⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hbound := strong_stationary_bound (topToRandom (m0 + 2)) (ttr_stochastic hn0)
    (ttr_irred m0) (uniformDist (Equiv.Perm (Fin (m0 + 2)))) (ttr_stationary hn0)
    (topToRandomRule (m0 + 2))
    (fun x => top_to_random_strong_stationary (m0 + 2) hn x) t
  have hconst : ∀ x : Equiv.Perm (Fin (m0 + 2)),
      stopTailProb (topToRandom (m0 + 2)) x (topToRandomRule (m0 + 2)) t
        = dsurvR (m0 + 2) s (m0 + 2 - 1) := by
    intro x
    rw [hs]
    exact stopTail_val (m0 + 2) hn0 x s
  rw [show (⨆ x : Equiv.Perm (Fin (m0 + 2)),
      stopTailProb (topToRandom (m0 + 2)) x (topToRandomRule (m0 + 2)) t)
      = dsurvR (m0 + 2) s (m0 + 2 - 1) from by
        simp only [hconst]
        exact ciSup_const] at hbound
  refine hbound.trans ?_
  refine (dsurv_bound (m0 + 2) s (by omega)).trans ?_
  rw [← hs]
  exact numeric_bound (m0 + 2) hn α t (Nat.le_ceil _)
