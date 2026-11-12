-- Prove2me | solution 1 for NarrowDNF.Approx.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T01:54:26.512119+00:00
-- url     : https://prove2.me/submissions/276d26a8-3c50-437e-81ad-88d4985e8f16

import Mathlib
import Definitions.Def_NarrowDNF_Approx_Activation

section
set_option autoImplicit false
namespace NarrowDNF.Dev.L34
open NarrowDNF.Approx

noncomputable def wt {n : ℕ} (p : ℝ) (x : Cube n) : ℝ := ∏ i : Fin n, FriedgutCoalition.bern p (x i)

lemma prob_eq {n : ℕ} (p : ℝ) (E : Cube n → Prop) [DecidablePred E] :
    prob p E = ∑ x : Cube n, if E x then wt p x else 0 := by
  unfold prob FriedgutCoalition.wProb wt
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h : E x <;> simp [h]

lemma sum_prod_cube {ι : Type} [Fintype ι] [DecidableEq ι] (g : ι → Bool → ℝ) :
    ∑ x : ι → Bool, ∏ i, g i (x i) = ∏ i, ∑ b : Bool, g i b := by
  have := Finset.prod_univ_sum (fun i : ι => (Finset.univ : Finset Bool)) g
  rw [this, Fintype.piFinset_univ]

lemma bern_sum (p : ℝ) : ∑ b : Bool, FriedgutCoalition.bern p b = 1 := by
  simp [FriedgutCoalition.bern]

lemma wt_nonneg {n : ℕ} (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (x : Cube n) : 0 ≤ wt p x :=
  Finset.prod_nonneg (fun j _ => by
    simp only [FriedgutCoalition.bern]; split_ifs <;> linarith)

lemma expect_eq {n : ℕ} (p : ℝ) (c : Cube n → ℝ) :
    expect p c = ∑ x : Cube n, wt p x * c x := rfl

/-- marginal formula -/
lemma prob_marg {n : ℕ} (σ : ℝ) (S : Finset (Fin n)) (P : (S → Bool) → Prop) [DecidablePred P] :
    prob σ (fun x : Cube n => P (fun i => x i)) =
      ∑ s : S → Bool, if P s then ∏ i : S, FriedgutCoalition.bern σ (s i) else 0 := by
  classical
  rw [prob_eq]
  let e := Equiv.piEquivPiSubtypeProd (fun i : Fin n => i ∈ S) (fun _ => Bool)
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  have hx : ∀ t : {i : Fin n // i ∉ S} → Bool, (fun i : S => (e.symm (s, t)) i) = s := by
    intro t; funext i
    simp [e, Equiv.piEquivPiSubtypeProd_symm_apply]
  have hw : ∀ t : {i : Fin n // i ∉ S} → Bool, wt σ (e.symm (s, t)) =
      (∏ i : S, FriedgutCoalition.bern σ (s i)) *
        ∏ i : {i : Fin n // i ∉ S}, FriedgutCoalition.bern σ (t i) := by
    intro t
    unfold wt
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : Fin n => i ∈ S)]
    congr 1
    · refine Finset.prod_congr (by ext; simp) (fun i _ => ?_)
      simp [e, Equiv.piEquivPiSubtypeProd_symm_apply]
    · refine Finset.prod_congr (by ext; simp) (fun i _ => ?_)
      simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, i.2]
  simp only [hx, hw]
  by_cases hP : P s
  · simp only [hP, if_true]
    rw [← Finset.mul_sum]
    have : ∑ t : {i : Fin n // i ∉ S} → Bool, ∏ i : {i : Fin n // i ∉ S}, FriedgutCoalition.bern σ (t i) = 1 := by
      rw [sum_prod_cube (fun _ b => FriedgutCoalition.bern σ b)]
      simp only [bern_sum, Finset.prod_const_one]
    rw [this, mul_one]
  · simp [hP]

section pair
open Classical

lemma bern_or_sum (p : ℝ) (c : Bool) :
    ∑ a : Bool, ∑ b : Bool, (if (a || b) = c then FriedgutCoalition.bern p a * FriedgutCoalition.bern p b else 0)
      = FriedgutCoalition.bern (2 * p - p ^ 2) c := by
  cases c <;> simp [FriedgutCoalition.bern] <;> ring

lemma pair_key {n : ℕ} (p : ℝ) (y : Cube n) :
    ∑ x : Cube n, ∑ z : Cube n, (if (fun j => x j || z j) = y then wt p x * wt p z else 0)
      = wt (2 * p - p ^ 2) y := by
  have h1 : ∀ x z : Cube n, (if (fun j => x j || z j) = y then wt p x * wt p z else 0) =
      ∏ i, (if (x i || z i) = y i then FriedgutCoalition.bern p (x i) * FriedgutCoalition.bern p (z i) else 0) := by
    intro x z
    by_cases h : (fun j => x j || z j) = y
    · have h' : ∀ i, (x i || z i) = y i := fun i => congrFun h i
      simp only [h, if_true, h', wt, Finset.prod_mul_distrib]
    · have : ∃ i, (x i || z i) ≠ y i := by
        by_contra hc; exact h (funext (fun i => by by_contra hh; exact hc ⟨i, hh⟩))
      obtain ⟨i, hi⟩ := this
      rw [if_neg h]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  simp only [h1]
  have h2 : ∀ x : Cube n, ∑ z : Cube n, ∏ i, (if (x i || z i) = y i then FriedgutCoalition.bern p (x i) * FriedgutCoalition.bern p (z i) else 0)
      = ∏ i, ∑ b : Bool, (if (x i || b) = y i then FriedgutCoalition.bern p (x i) * FriedgutCoalition.bern p b else 0) := by
    intro x
    exact sum_prod_cube (fun i b => if (x i || b) = y i then FriedgutCoalition.bern p (x i) * FriedgutCoalition.bern p b else 0)
  simp only [h2]
  rw [sum_prod_cube (fun i a => ∑ b : Bool, (if (a || b) = y i then FriedgutCoalition.bern p a * FriedgutCoalition.bern p b else 0))]
  unfold wt
  exact Finset.prod_congr rfl (fun i _ => bern_or_sum p (y i))

lemma pair_sum {n : ℕ} (p : ℝ) (G : Cube n → ℝ) :
    ∑ x : Cube n, ∑ z : Cube n, wt p x * wt p z * G (fun j => x j || z j)
      = ∑ y : Cube n, wt (2 * p - p ^ 2) y * G y := by
  have h1 : ∀ x z : Cube n, wt p x * wt p z * G (fun j => x j || z j) =
      ∑ y : Cube n, (if (fun j => x j || z j) = y then wt p x * wt p z else 0) * G y := by
    intro x z
    simp [ite_mul]
  simp only [h1]
  have h3 : ∀ x : Cube n, ∑ z : Cube n, ∑ y : Cube n,
      (if (fun j => x j || z j) = y then wt p x * wt p z else 0) * G y =
      ∑ y : Cube n, ∑ z : Cube n, (if (fun j => x j || z j) = y then wt p x * wt p z else 0) * G y :=
    fun x => Finset.sum_comm
  simp only [h3]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [← pair_key p y, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_mul]

end pair

section main
open Classical

lemma force_eval {n : ℕ} (J : ActivationFamily n) (z x : Cube n) (S : Finset (Fin n)) :
    force J (ones z) S (fun i => x i) = J S (fun i => x i || z i) := by
  unfold force
  congr 1
  funext i
  by_cases h : z i = true <;> simp [ones, h]

lemma part1 {n : ℕ} (p : ℝ) (J : ActivationFamily n) :
    expect p (fun z => load p (force J (ones z))) = load (2 * p - p ^ 2) J := by
  unfold load
  rw [expect_eq]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  have h1 : ∀ z : Cube n, wt p z * ((S.card : ℝ) * prob p (fun x : Cube n => force J (ones z) S (fun i => x i) = true))
      = (S.card : ℝ) * ∑ x : Cube n, wt p x * wt p z *
          (if J S (fun i => (fun j => x j || z j) i) = true then 1 else 0) := by
    intro z
    rw [prob_eq]
    simp only [force_eval]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : J S (fun i => x i || z i) = true <;> simp [h] <;> ring
  simp only [h1]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  have := pair_sum p (fun y : Cube n => if J S (fun i => y i) = true then (1:ℝ) else 0)
  rw [prob_eq]
  simp only [mul_ite, mul_one, mul_zero] at this ⊢
  rw [← this]

lemma bern_le {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (b : Bool) :
    FriedgutCoalition.bern (2 * p - p ^ 2) b ≤ (2 - p) * FriedgutCoalition.bern p b := by
  cases b <;> simp [FriedgutCoalition.bern] <;> nlinarith

lemma bern_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ FriedgutCoalition.bern p b := by
  cases b <;> simp [FriedgutCoalition.bern] <;> linarith

lemma prob_q_le {n : ℕ} (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (d : ℕ) (J : ActivationFamily n)
    (hd : ArityLE J d) (S : Finset (Fin n)) :
    prob (2 * p - p ^ 2) (fun x : Cube n => J S (fun i => x i) = true) ≤
      (2 - p) ^ d * prob p (fun x : Cube n => J S (fun i => x i) = true) := by
  rw [prob_marg (2 * p - p ^ 2) S (fun s => J S s = true), prob_marg p S (fun s => J S s = true),
    Finset.mul_sum]
  by_cases hS : d < S.card
  · have : ∀ s, J S s = false := hd S hS
    simp [this]
  · push Not at hS
    refine Finset.sum_le_sum (fun s _ => ?_)
    by_cases hs : J S s = true
    · simp only [hs, if_true]
      calc ∏ i : S, FriedgutCoalition.bern (2 * p - p ^ 2) (s i)
          ≤ ∏ i : S, ((2 - p) * FriedgutCoalition.bern p (s i)) :=
            Finset.prod_le_prod (fun i _ => bern_nonneg (by nlinarith) (by nlinarith) _)
              (fun i _ => bern_le hp hp1 _)
        _ = (2 - p) ^ S.card * ∏ i : S, FriedgutCoalition.bern p (s i) := by
            rw [Finset.prod_mul_distrib]; simp
        _ ≤ (2 - p) ^ d * ∏ i : S, FriedgutCoalition.bern p (s i) := by
            refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) hS) ?_
            exact Finset.prod_nonneg (fun i _ => bern_nonneg hp.le hp1.le _)
    · simp [hs]

lemma card_le {n : ℕ} (J : ActivationFamily n) (x : Cube n) :
    (activeUnion J x).card ≤ ∑ S : Finset (Fin n), if J S (fun i => x i) = true then S.card else 0 := by
  unfold activeUnion
  refine (Finset.card_biUnion_le).trans ?_
  rw [Finset.sum_filter]
  exact le_of_eq (by simp)

lemma activeCost_le {n : ℕ} (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (J : ActivationFamily n) :
    activeCost p J ≤ load p J := by
  unfold activeCost load
  rw [expect_eq]
  have h1 : ∀ x : Cube n, wt p x * ((activeUnion J x).card : ℝ) ≤
      ∑ S : Finset (Fin n), (S.card : ℝ) * (if J S (fun i => x i) = true then wt p x else 0) := by
    intro x
    have h := card_le J x
    have h' : ((activeUnion J x).card : ℝ) ≤
        ∑ S : Finset (Fin n), if J S (fun i => x i) = true then (S.card : ℝ) else 0 := by
      exact_mod_cast (h.trans (le_of_eq (by simp)))
    calc wt p x * ((activeUnion J x).card : ℝ)
        ≤ wt p x * ∑ S : Finset (Fin n), if J S (fun i => x i) = true then (S.card : ℝ) else 0 :=
          mul_le_mul_of_nonneg_left h' (wt_nonneg p hp.le hp1.le x)
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun S _ => ?_)
          by_cases h : J S (fun i => x i) = true <;> simp [h, mul_comm]
  refine (Finset.sum_le_sum (fun x _ => h1 x)).trans ?_
  rw [Finset.sum_comm]
  refine le_of_eq (Finset.sum_congr rfl (fun S _ => ?_))
  rw [prob_eq, ← Finset.mul_sum]

end main

end NarrowDNF.Dev.L34

namespace NarrowDNF.Approx
open NarrowDNF.Dev.L34 in
theorem chk_lemma_3_4 {n : ℕ} (p : ℝ) (d : ℕ) (J : ActivationFamily n)
    (hp : 0 < p) (hp_one : p < 1) (hd : ArityLE J d) :
    expect p (fun z => load p (force J (ones z))) = load (2 * p - p ^ 2) J ∧
    load (2 * p - p ^ 2) J ≤ (2 - p) ^ d * load p J ∧
    (2 - p) ^ d * load p J ≤ (2 : ℝ) ^ d * load p J ∧
    expect p (fun z => activeCost p (force J (ones z))) ≤ (2 - p) ^ d * load p J := by
  have h2 : load (2 * p - p ^ 2) J ≤ (2 - p) ^ d * load p J := by
    unfold load
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun S _ => ?_)
    have := prob_q_le p hp hp_one d J hd S
    have hc : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    calc (S.card : ℝ) * prob (2 * p - p ^ 2) (fun x : Cube n => J S (fun i => x i) = true)
        ≤ (S.card : ℝ) * ((2 - p) ^ d * prob p (fun x : Cube n => J S (fun i => x i) = true)) :=
          mul_le_mul_of_nonneg_left this hc
      _ = _ := by ring
  have hl : 0 ≤ load p J := by
    unfold load
    refine Finset.sum_nonneg (fun S _ => mul_nonneg (Nat.cast_nonneg _) ?_)
    rw [prob_eq]
    exact Finset.sum_nonneg (fun x _ => by
      split_ifs
      · exact wt_nonneg p hp.le hp_one.le x
      · exact le_refl _)
  refine ⟨part1 p J, h2, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (by linarith) d) hl
  · calc expect p (fun z => activeCost p (force J (ones z)))
        ≤ expect p (fun z => load p (force J (ones z))) := by
          rw [expect_eq, expect_eq]
          exact Finset.sum_le_sum (fun z _ =>
            mul_le_mul_of_nonneg_left (activeCost_le p hp hp_one _) (wt_nonneg p hp.le hp_one.le z))
      _ ≤ _ := by rw [part1]; exact h2

end NarrowDNF.Approx
end

theorem solution : type_of% @NarrowDNF.Approx.chk_lemma_3_4 := @NarrowDNF.Approx.chk_lemma_3_4
