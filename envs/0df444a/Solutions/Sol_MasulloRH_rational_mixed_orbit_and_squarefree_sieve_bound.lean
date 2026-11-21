-- Prove2me | solution 1 for MasulloRH.rational_mixed_orbit_and_squarefree_sieve_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T04:33:42.809871+00:00
-- url     : https://prove2.me/submissions/2d639e06-3e65-4c96-bf96-a9d1ce1ee3cd

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open Filter Finset
open scoped Topology

private def signedWindow (N : ℕ) : Finset ℤ :=
  ((range N).image Int.ofNat) ∪ ((range N).image Int.negSucc)

private lemma window_limit (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    Tendsto (fun N : ℕ => ∑ j ∈ signedWindow N, r ^ j.natAbs)
      atTop (𝓝 ((1+r)/(1-r))) := by
  have hw (N : ℕ) : ∑ j ∈ signedWindow N, r^j.natAbs =
      (∑ j ∈ range N, r^j) + (∑ j ∈ range N, r^j)*r := by
    have hd : Disjoint ((range N).image Int.ofNat) ((range N).image Int.negSucc) := by
      refine Finset.disjoint_left.mpr ?_
      intro x hx hy
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨k,_,h⟩ := Finset.mem_image.mp hy
      contradiction
    simp only [signedWindow, Finset.sum_union hd]
    rw [Finset.sum_image (fun _ _ _ _ h => Int.ofNat.inj h),
      Finset.sum_image (fun _ _ _ _ h => Int.negSucc.inj h)]
    simp [pow_succ, Finset.sum_mul]
  simp_rw [hw]
  have hs := (hasSum_geometric_of_lt_one hr.le hr1).tendsto_sum_nat
  have hc : (1+r)/(1-r) = (1-r)⁻¹ + (1-r)⁻¹ * r := by
    field_simp [(sub_pos.mpr hr1).ne']
  rw [hc]
  exact hs.add (hs.mul_const r)

private theorem mixed_bound {I G : Type*} [Fintype I] [DecidableEq I]
    (r : I → ℝ) (hr : ∀ i, 0 < r i) (hr1 : ∀ i, r i < 1)
    (C : G → ℝ) (hC : ∀ x, 0 ≤ C x) (hm : HasSum C 1)
    (e : (I → ℤ) ↪ G) (c : ℝ)
    (h : ∀ k : I → ℤ, c * ∏ i, (r i)^(k i).natAbs ≤ C (e k)) :
    c ≤ ∏ i, (1-r i)/(1+r i) := by
  classical
  have hpartial (N : ℕ) : c * ∏ i, (∑ j ∈ signedWindow N, (r i)^j.natAbs) ≤ 1 := by
    let S := Fintype.piFinset (fun _ : I => signedWindow N)
    rw [Finset.prod_univ_sum, Finset.mul_sum]
    calc
      _ ≤ ∑ k ∈ S, C (e k) := Finset.sum_le_sum (fun k _ => h k)
      _ = ∑ g ∈ S.map e, C g := (Finset.sum_map ..).symm
      _ ≤ 1 := sum_le_hasSum _ (fun g _ => hC g) hm
  have hlim := tendsto_finsetProd (s := (univ : Finset I))
    (fun i _ => window_limit (r i) (hr i) (hr1 i))
  have hb : c * (∏ i, (1+r i)/(1-r i)) ≤ 1 :=
    le_of_tendsto (hlim.const_mul c) (Eventually.of_forall hpartial)
  have hden : 0 < ∏ i, (1+r i)/(1-r i) := Finset.prod_pos (fun i _ =>
    div_pos (by linarith [hr i]) (sub_pos.mpr (hr1 i)))
  have hc := (le_div_iff₀ hden).mpr hb
  simpa only [one_div, ← Finset.prod_inv_distrib, inv_div] using hc

private theorem rat_prime_shift_injective (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    Function.Injective (fun k : P → ℤ => ∏ p : P, ((p.val : ℚ) ^ k p)) := by
  classical
  have extract (p : P) (k : P → ℤ) :
      padicValRat p.val (∏ q : P, ((q.val : ℚ) ^ k q)) = k p := by
    let : Fact p.val.Prime := ⟨hP p p.property⟩
    have hn (q : P) : (q.val : ℚ) ≠ 0 := by exact_mod_cast (hP q q.property).ne_zero
    have hpairs (q : P) (hq : q ≠ p) : padicValRat p.val (q.val : ℚ) = 0 := by
      have hne : p.val ≠ q.val := fun e => hq (Subtype.ext e.symm)
      have hd : ¬ p.val ∣ q.val := fun h => hne ((Nat.prime_dvd_prime_iff_eq
        (hP p p.property) (hP q q.property)).mp h)
      simp [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hd]
    have hprod (S : Finset P) :
        padicValRat p.val (∏ q ∈ S, (q.val : ℚ) ^ k q) =
          ∑ q ∈ S, k q * padicValRat p.val (q.val : ℚ) := by
      induction S using Finset.induction_on with
      | empty => simp
      | @insert q S hq ih =>
        rw [Finset.prod_insert hq, Finset.sum_insert hq,
          padicValRat.mul (zpow_ne_zero _ (hn q)) (Finset.prod_ne_zero_iff.mpr
            (fun j _ => zpow_ne_zero _ (hn j))), padicValRat.zpow, ih]
    rw [hprod, Finset.sum_eq_single p]
    · simp [padicValRat.self (hP p p.property).one_lt]
    · intro q _ hq
      rw [hpairs q hq, mul_zero]
    · simp
  intro k l hkl
  funext p
  rw [← extract p k, ← extract p l]
  exact congrArg (padicValRat p.val) hkl


private lemma one_sum_le_product (s : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    1 + ∑ n ∈ s, f n ≤ ∏ n ∈ s, (1+f n) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx]
    have hp := mul_nonneg (hf x) (Finset.sum_nonneg (fun i (_ : i ∈ s) => hf i))
    have hmul := mul_le_mul_of_nonneg_left ih (by linarith [hf x] : 0 ≤ 1+f x)
    linarith

private theorem cubic_tail (a : ℝ) (ha : 0 < a) (ha' : a ≤ 1) :
    Tendsto (fun B : ℕ => ∏ p ∈ (range (B+1)).filter Nat.Prime,
      (1-(p:ℝ)^(-a))*(1+2*(p:ℝ)^(-a))) atTop atTop := by
  let f (n : ℕ) : ℝ := if n.Prime then (n:ℝ)^(-a) else 0
  have hf (n : ℕ) : 0 ≤ f n := by dsimp [f]; split_ifs <;> positivity
  have hsmall (n : ℕ) : f n < 1 := by
    dsimp [f]
    split_ifs with h
    · exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast h.one_lt) (neg_lt_zero.mpr ha)
    · norm_num
  have hf0 : Tendsto f atTop (𝓝 0) := by
    apply squeeze_zero hf (fun n => ?_) ((tendsto_rpow_neg_atTop ha).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
    dsimp [f]
    split_ifs <;> first | rfl | positivity
  obtain ⟨D,hD⟩ := eventually_atTop.mp (hf0.eventually_lt_const (show (0:ℝ)<1/4 by norm_num))
  let g (n : ℕ) := (1-f n)*(1+2*f n)
  have hg (n : ℕ) : 0 < g n := mul_pos (sub_pos.mpr (hsmall n)) (by linarith [hf n])
  have hh (n : ℕ) : 1 + f (D+n)/2 ≤ g (D+n) := by
    have hN := hD (D+n) (Nat.le_add_right _ _)
    have ha₁ := mul_nonneg (hf (D+n)) (sub_nonneg.mpr hN.le)
    dsimp [g]
    nlinarith
  have hns : ¬ Summable f := by
    intro h
    have hx := Nat.Primes.summable_rpow.mp <|
      (Nat.Primes.summable_iff_summable_ite (fun n : ℕ => (n:ℝ)^(-a))).mpr h
    linarith
  have hns' : ¬ Summable (fun n => f (D+n)/2) := by
    intro h
    have hj := h.mul_left 2
    have hj' : Summable (fun n => f (n+D)) := by
      simpa only [Nat.add_comm D, ← mul_div_assoc, mul_div_cancel_left₀ _ (show (2:ℝ) ≠ 0 by norm_num)] using hj
    exact hns ((summable_nat_add_iff D).mp hj')
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun n => div_nonneg (hf (D+n)) (by norm_num : (0:ℝ) ≤ 2))).mp hns'
  have hpt : Tendsto (fun N : ℕ => ∏ n ∈ range N, g (D+n)) atTop atTop := by
    apply tendsto_atTop_mono (fun N => ?_) ht
    calc
      _ ≤ 1 + ∑ n ∈ range N, f (D+n)/2 := by linarith
      _ ≤ ∏ n ∈ range N, (1+f (D+n)/2) := one_sum_le_product _ _
        (fun n => div_nonneg (hf _) (by norm_num))
      _ ≤ _ := Finset.prod_le_prod (fun n _ => by linarith [hf (D+n)]) (fun n _ => hh n)
  have hall : Tendsto (fun N : ℕ => ∏ n ∈ range N, g n) atTop atTop := by
    apply (tendsto_add_atTop_iff_nat D).mp
    have H := hpt.const_mul_atTop (Finset.prod_pos (s := range D) (fun n _ => hg n))
    simpa only [Nat.add_comm _ D, Finset.prod_range_add] using! H
  have H := hall.comp (tendsto_add_atTop_nat 1)
  convert H using 1
  ext B
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro n _
  by_cases h : n.Prime <;> simp [g,f,h]

private theorem square_bound {I G : Type*} [Fintype I] [DecidableEq I]
    (r : I → ℝ) (C : G → ℝ) (hC : ∀ x, 0 ≤ C x) (hm : HasSum C 1)
    (e : (I → ℤ) ↪ G) (c : ℝ)
    (h : ∀ k : I → ℤ, (∀ i, (k i).natAbs ≤ 1) →
      c * ∏ i, (r i)^(k i).natAbs ≤ C (e k)) :
    c * (∏ i : I, (1+2*r i)) ≤ 1 := by
  classical
  let box : Finset ℤ := {-1,0,1}
  have he (i : I) : (1+2*r i) = ∑ j ∈ box, (r i)^j.natAbs := by simp [box]; ring
  simp_rw [he]
  rw [Finset.prod_univ_sum, Finset.mul_sum]
  let S := Fintype.piFinset (fun _ : I => box)
  calc
    _ ≤ ∑ k ∈ S, C (e k) := Finset.sum_le_sum (fun k hk => h k (by
      intro i
      have hki := (Fintype.mem_piFinset.mp hk) i
      change k i ∈ box at hki
      simp only [box, mem_insert, mem_singleton] at hki
      rcases hki with hl | hl | hl <;> rw [hl] <;> decide))
    _ = ∑ g ∈ S.map e, C g := (Finset.sum_map ..).symm
    _ ≤ 1 := sum_le_hasSum _ (fun g _ => hC g) hm

theorem solution (a : ℝ) (ha : 0 < a) (ha' : a ≤ 1)
    (C : ℕ → ℚ → ℝ) (hC : ∀ B x, 0 ≤ C B x) (hm : ∀ B, HasSum (C B) 1) :
    let P (B : ℕ) := (range (B+1)).filter Nat.Prime
    let r (p : ℕ) := (p : ℝ)^(-a)
    let E (B : ℕ) := ∏ p ∈ P B, (1-r p)
    (∀ B : ℕ, (∀ k : P B → ℤ, C B 1 * (∏ p : P B, (r p.val)^(k p).natAbs) ≤
        C B (∏ p : P B, (p.val : ℚ)^(k p))) →
      C B 1 ≤ ∏ p ∈ P B, (1-r p)/(1+r p)) ∧
    ((∀ (B : ℕ) (k : P B → ℤ), (∀ p, (k p).natAbs ≤ 1) →
        C B 1 * (∏ p : P B, (r p.val)^(k p).natAbs) ≤
          C B (∏ p : P B, (p.val : ℚ)^(k p))) →
      (∀ B : ℕ, C B 1 * (∏ p ∈ P B, (1+2*r p)) ≤ 1) ∧
      Tendsto (fun B => C B 1/E B) atTop (𝓝 0)) := by
  classical
  intro P r E
  have hP (B : ℕ) (p : ℕ) (hp : p ∈ P B) : p.Prime := (Finset.mem_filter.mp hp).2
  let emb (B : ℕ) : (P B → ℤ) ↪ ℚ := ⟨_, rat_prime_shift_injective (P B) (hP B)⟩
  have hr (B : ℕ) (p : P B) : 0 < r p.val :=
    Real.rpow_pos_of_pos (by exact_mod_cast (hP B p.val p.property).pos) _
  have hlt (B : ℕ) (p : P B) : r p.val < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (hP B p.val p.property).one_lt)
      (neg_lt_zero.mpr ha)
  constructor
  · intro B h
    have H := mixed_bound (fun p : P B => r p.val) (hr B) (hlt B) (C B) (hC B) (hm B) (emb B)
      (C B 1) h
    rw [← Finset.prod_coe_sort (P B) (fun p => (1-r p)/(1+r p))]
    exact H
  intro h
  let den (B : ℕ) := ∏ p ∈ P B, (1+2*r p)
  have hb (B : ℕ) : C B 1 * den B ≤ 1 := by
    have H := square_bound (fun p : P B => r p.val) (C B) (hC B) (hm B) (emb B) (C B 1) (h B)
    dsimp only [den]
    rw [← Finset.prod_coe_sort (P B) (fun p => (1+2*r p))]
    exact H
  refine ⟨hb, ?_⟩
  have hE (B : ℕ) : 0 < E B := Finset.prod_pos (fun p hp => sub_pos.mpr (hlt B ⟨p,hp⟩))
  have hden (B : ℕ) : 0 < den B :=
    Finset.prod_pos (fun p hp => by have := hr B ⟨p,hp⟩; dsimp at this; linarith)
  have htop : Tendsto (fun B => E B * den B) atTop atTop := by
    simpa only [E,den,← Finset.prod_mul_distrib] using! cubic_tail a ha ha'
  apply squeeze_zero (fun B => div_nonneg (hC B 1) (hE B).le) _ htop.inv_tendsto_atTop
  intro B
  change C B 1 / E B ≤ (E B * den B)⁻¹
  rw [← one_div, ← div_div, div_right_comm]
  exact div_le_div_of_nonneg_right ((le_div_iff₀ (hden B)).mpr (hb B)) (hE B).le
