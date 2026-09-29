-- Prove2me | solution 1 for MarkovMixing.coupon_expectation
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T20:25:43.126579+00:00
-- url     : https://prove2.me/submissions/8ea618e3-e428-4380-91e9-dc9a82279cc1

import Definitions.Def_mm_classical
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Coupon collector expectation (LPW Proposition 2.3)
-/

namespace MarkovMixing

noncomputable section
open scoped BigOperators
open Finset

/-- The number of maps into a prescribed target set. -/
private lemma card_maps_into (n t : ℕ) (B : Finset (Fin n)) :
    ((univ.filter fun d : Fin t → Fin n => ∀ i, d i ∈ B).card) = B.card ^ t := by
  have hset : (univ.filter fun d : Fin t → Fin n => ∀ i, d i ∈ B)
      = Fintype.piFinset (fun _ : Fin t => B) := by
    ext d; simp [Fintype.mem_piFinset]
  rw [hset, Fintype.card_piFinset_const]

/-- Inclusion–exclusion count of the surjections `Fin t → Fin n`. -/
private lemma card_surj (n t : ℕ) :
    ((univ.filter fun d : Fin t → Fin n => Function.Surjective d).card : ℤ)
      = ∑ S : Finset (Fin n), (-1) ^ S.card * (((n - S.card : ℕ) : ℤ)) ^ t := by
  classical
  have hcard : ∀ S : Finset (Fin n), (Sᶜ).card = n - S.card := by
    intro S; rw [Finset.card_compl, Fintype.card_fin]
  have key : ∀ S : Finset (Fin n),
      ((-1 : ℤ) ^ S.card * (((n - S.card : ℕ) : ℤ)) ^ t)
        = ∑ d : Fin t → Fin n,
            (if ∀ i, d i ∈ Sᶜ then ((-1 : ℤ) ^ S.card) else 0) := by
    intro S
    have h1 : (((n - S.card : ℕ) : ℤ)) ^ t
        = ((univ.filter fun d : Fin t → Fin n => ∀ i, d i ∈ Sᶜ).card : ℤ) := by
      rw [card_maps_into n t Sᶜ, hcard S, Nat.cast_pow]
    rw [h1, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hd : ∀ i, d i ∈ Sᶜ <;> simp [hd]
  have inner : ∀ d : Fin t → Fin n,
      (∑ S : Finset (Fin n), (if ∀ i, d i ∈ Sᶜ then ((-1 : ℤ)) ^ S.card else 0))
        = if Function.Surjective d then 1 else 0 := by
    intro d
    have hcond : ∀ S : Finset (Fin n), (∀ i, d i ∈ Sᶜ) ↔ S ⊆ (univ.image d)ᶜ := by
      intro S
      constructor
      · intro h y hy
        rw [Finset.mem_compl, Finset.mem_image]
        rintro ⟨i, -, rfl⟩
        exact (Finset.mem_compl.mp (h i)) hy
      · intro h i
        rw [Finset.mem_compl]
        intro hmem
        have h2 := h hmem
        rw [Finset.mem_compl] at h2
        exact h2 (Finset.mem_image_of_mem d (Finset.mem_univ i))
    calc (∑ S : Finset (Fin n), (if ∀ i, d i ∈ Sᶜ then ((-1 : ℤ)) ^ S.card else 0))
        = ∑ S : Finset (Fin n),
            (if S ⊆ (univ.image d)ᶜ then ((-1 : ℤ)) ^ S.card else 0) :=
          Finset.sum_congr rfl fun S _ => by rw [if_congr (hcond S) rfl rfl]
      _ = ∑ S ∈ ((univ.image d)ᶜ).powerset, ((-1 : ℤ)) ^ S.card := by
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ fun S _ => rfl
          ext S
          simp [Finset.mem_powerset]
      _ = if ((univ.image d)ᶜ) = ∅ then 1 else 0 :=
          Finset.sum_powerset_neg_one_pow_card
      _ = if Function.Surjective d then 1 else 0 := by
          by_cases hs : Function.Surjective d
          · rw [if_pos hs, if_pos]
            rw [Finset.compl_eq_empty_iff, Finset.eq_univ_iff_forall]
            intro y
            obtain ⟨i, hi⟩ := hs y
            exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
          · rw [if_neg hs, if_neg]
            intro hcon
            apply hs
            rw [Finset.compl_eq_empty_iff, Finset.eq_univ_iff_forall] at hcon
            intro y
            obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (hcon y)
            exact ⟨i, hi⟩
  rw [Finset.sum_congr rfl fun S _ => key S, Finset.sum_comm,
    Finset.sum_congr rfl fun d _ => inner d, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hs : Function.Surjective d <;> simp [hs]

/-- The real form of the vanishing alternating binomial sum. -/
private lemma alt_choose_zero (N : ℕ) (hN : N ≠ 0) :
    ∑ m ∈ Finset.range (N + 1), (-1 : ℝ) ^ m * (N.choose m : ℝ) = 0 := by
  have h := Int.alternating_sum_range_choose_of_ne hN
  have := congrArg (fun z : ℤ => (z : ℝ)) h
  push_cast at this
  simpa using this

/-- `∑_{j<n} (-1)^j C(n,j+1)/(j+1) = ∑_{j<n} 1/(j+1)`. -/
private lemma alt_harmonic (n : ℕ) :
    ∑ j ∈ Finset.range n, (-1 : ℝ) ^ j * (n.choose (j + 1) : ℝ) / (j + 1)
      = ∑ j ∈ Finset.range n, (1 : ℝ) / (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : ∀ j : ℕ,
        (-1 : ℝ) ^ j * ((n + 1).choose (j + 1) : ℝ) / (j + 1)
          = (-1 : ℝ) ^ j * (n.choose j : ℝ) / (j + 1)
            + (-1 : ℝ) ^ j * (n.choose (j + 1) : ℝ) / (j + 1) := by
      intro j
      rw [Nat.choose_succ_succ n j]
      push_cast
      ring
    have hpos : ∀ j : ℕ, ((j : ℝ) + 1) ≠ 0 := by
      intro j; positivity
    -- the "shifted" half is the previous instance of the identity
    have hA : ∑ j ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ j * (n.choose (j + 1) : ℝ) / (j + 1)
        = ∑ j ∈ Finset.range n, (1 : ℝ) / (j + 1) := by
      rw [Finset.sum_range_succ, Nat.choose_succ_self]
      simp [ih]
    -- the "diagonal" half telescopes to 1/(n+1)
    have hkey : ∀ j : ℕ, (-1 : ℝ) ^ j * (n.choose j : ℝ) / (j + 1)
        = (-1 : ℝ) ^ j * ((n + 1).choose (j + 1) : ℝ) / (n + 1) := by
      intro j
      have h := Nat.add_one_mul_choose_eq n j
      have h' : ((n : ℝ) + 1) * (n.choose j : ℝ)
          = ((n + 1).choose (j + 1) : ℝ) * ((j : ℝ) + 1) := by
        have := congrArg (fun k : ℕ => (k : ℝ)) h
        push_cast at this
        linarith [this]
      field_simp
      nlinarith [h']
    have hB : ∑ j ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ j * (n.choose j : ℝ) / (j + 1) = 1 / (n + 1) := by
      have hre : ∑ j ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ j * (n.choose j : ℝ) / (j + 1)
          = (∑ j ∈ Finset.range (n + 1),
              (-1 : ℝ) ^ j * ((n + 1).choose (j + 1) : ℝ)) / (n + 1) := by
        simp only [hkey, div_eq_mul_inv, ← Finset.sum_mul]
      have halt : ∑ j ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ j * ((n + 1).choose (j + 1) : ℝ) = 1 := by
        have h0 := alt_choose_zero (n + 1) (Nat.succ_ne_zero n)
        rw [Finset.sum_range_succ'] at h0
        simp only [Nat.choose_zero_right, pow_zero, Nat.cast_one, mul_one] at h0
        have : ∑ j ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ (j + 1) * ((n + 1).choose (j + 1) : ℝ) = -1 := by linarith
        have hneg : ∀ j : ℕ, (-1 : ℝ) ^ (j + 1) * ((n + 1).choose (j + 1) : ℝ)
            = -((-1 : ℝ) ^ j * ((n + 1).choose (j + 1) : ℝ)) := by
          intro j; rw [pow_succ]; ring
        rw [Finset.sum_congr rfl fun j _ => hneg j, Finset.sum_neg_distrib] at this
        linarith
      rw [hre, halt]
    rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib, hA, hB,
      Finset.sum_range_succ]
    ring

private lemma sum_div' {α : Type*} (s : Finset α) (f : α → ℝ) (c : ℝ) :
    (∑ i ∈ s, f i) / c = ∑ i ∈ s, f i / c := by
  simp [div_eq_mul_inv, Finset.sum_mul]

private lemma card_surj_real (n t : ℕ) :
    ((univ.filter fun d : Fin t → Fin n => Function.Surjective d).card : ℝ)
      = ∑ S : Finset (Fin n), (-1 : ℝ) ^ S.card * (((n - S.card : ℕ) : ℝ)) ^ t := by
  have h2 := congrArg (fun z : ℤ => (z : ℝ)) (card_surj n t)
  simp only [Int.cast_natCast, Int.cast_sum, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one] at h2
  exact h2

private lemma sum_group (n t : ℕ) :
    (∑ S : Finset (Fin n), (-1 : ℝ) ^ S.card * (((n - S.card : ℕ) : ℝ)) ^ t)
      = ∑ m ∈ Finset.range (n + 1),
          (n.choose m : ℝ) * ((-1 : ℝ) ^ m * (((n - m : ℕ) : ℝ)) ^ t) := by
  have h := Finset.sum_powerset_apply_card
    (fun m : ℕ => (-1 : ℝ) ^ m * (((n - m : ℕ) : ℝ)) ^ t)
    (x := (Finset.univ : Finset (Fin n)))
  rw [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at h
  rw [h]
  exact Finset.sum_congr rfl fun m _ => by rw [nsmul_eq_mul]

/-- Inclusion–exclusion form of `P{τ > t}`. -/
private lemma missProb_eq (n : ℕ) (hn : 1 ≤ n) (t : ℕ) :
    couponMissProb n t
      = ∑ j ∈ Finset.range n,
          (-1 : ℝ) ^ j * (n.choose (j + 1) : ℝ) *
            ((((n - (j + 1) : ℕ)) : ℝ) / n) ^ t := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnt : ((n : ℝ)) ^ t ≠ 0 := pow_ne_zero _ hn0
  have htot : (Finset.univ : Finset (Fin t → Fin n)).card = n ^ t := by
    rw [Finset.card_univ, Fintype.card_pi_const, Fintype.card_fin]
  have hsplit : ((univ.filter fun d : Fin t → Fin n => Function.Surjective d).card)
      + ((univ.filter fun d : Fin t → Fin n => ¬Function.Surjective d).card)
      = n ^ t := by
    rw [← htot]
    exact Finset.card_filter_add_card_filter_not _
  have hns : ((univ.filter fun d : Fin t → Fin n => ¬Function.Surjective d).card : ℝ)
      = (n : ℝ) ^ t
        - ((univ.filter fun d : Fin t → Fin n => Function.Surjective d).card : ℝ) := by
    have hc := congrArg (fun k : ℕ => (k : ℝ)) hsplit
    push_cast at hc
    linarith
  have hgroup := (card_surj_real n t).trans (sum_group n t)
  rw [Finset.sum_range_succ'] at hgroup
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul,
    Nat.sub_zero] at hgroup
  simp only [couponMissProb]
  rw [hns, hgroup]
  have hcollect : (n : ℝ) ^ t
        - (∑ j ∈ Finset.range n,
            (n.choose (j + 1) : ℝ) *
              ((-1 : ℝ) ^ (j + 1) * (((n - (j + 1) : ℕ) : ℝ)) ^ t) + (n : ℝ) ^ t)
      = ∑ j ∈ Finset.range n,
          (-((n.choose (j + 1) : ℝ) *
            ((-1 : ℝ) ^ (j + 1) * (((n - (j + 1) : ℕ) : ℝ)) ^ t))) := by
    rw [Finset.sum_neg_distrib]; ring
  rw [hcollect, sum_div']
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [div_pow, pow_succ]
  field_simp

end

end MarkovMixing

open MarkovMixing Finset

/-- **Proposition 2.3** (LPW): coupon collector expectation. -/
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    couponExpTime n = n * ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hrho : ∀ j ∈ Finset.range n,
      0 ≤ (((n - (j + 1) : ℕ)) : ℝ) / n ∧ (((n - (j + 1) : ℕ)) : ℝ) / n < 1 := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hlt : (n - (j + 1) : ℕ) < n := by omega
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one (by positivity)]
    exact_mod_cast hlt
  have hsum : ∀ j ∈ Finset.range n,
      Summable (fun t : ℕ => (-1 : ℝ) ^ j * (n.choose (j + 1) : ℝ) *
        ((((n - (j + 1) : ℕ)) : ℝ) / n) ^ t) := fun j hj =>
    (summable_geometric_of_lt_one (hrho j hj).1 (hrho j hj).2).mul_left _
  have hterm : ∀ j ∈ Finset.range n,
      (∑' t : ℕ, (-1 : ℝ) ^ j * (n.choose (j + 1) : ℝ) *
        ((((n - (j + 1) : ℕ)) : ℝ) / n) ^ t)
        = (-1 : ℝ) ^ j * (n.choose (j + 1) : ℝ) * ((n : ℝ) / (j + 1)) := by
    intro j hj
    rw [tsum_mul_left, tsum_geometric_of_lt_one (hrho j hj).1 (hrho j hj).2]
    congr 1
    rw [Finset.mem_range] at hj
    have hle : (j + 1) ≤ n := by omega
    have hcast : (((n - (j + 1) : ℕ)) : ℝ) = (n : ℝ) - ((j : ℝ) + 1) := by
      rw [Nat.cast_sub hle]; push_cast; ring
    rw [hcast]
    have hj1 : ((j : ℝ) + 1) ≠ 0 := by positivity
    rw [show (1 : ℝ) - ((n : ℝ) - ((j : ℝ) + 1)) / n = ((j : ℝ) + 1) / n by
      field_simp; ring]
    rw [inv_div]
  have hre : ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k
      = ∑ j ∈ Finset.range n, (1 : ℝ) / ((j : ℝ) + 1) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  simp only [couponExpTime]
  rw [tsum_congr (fun t => missProb_eq n hn t), Summable.tsum_finsetSum hsum,
    Finset.sum_congr rfl hterm, hre, ← alt_harmonic n, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj1 : ((j : ℝ) + 1) ≠ 0 := by positivity
  field_simp
