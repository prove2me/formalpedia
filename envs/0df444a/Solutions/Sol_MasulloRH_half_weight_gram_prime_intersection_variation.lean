-- Prove2me | solution 1 for MasulloRH.half_weight_gram_prime_intersection_variation
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T19:37:38.175418+00:00
-- url     : https://prove2.me/submissions/27497c5e-5136-4d5c-8321-1e823642d4c9

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
open Finset Filter
open scoped BigOperators Topology Classical

private theorem subset_sign_sum {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (E : Set ι) :
    (∑ J ∈ P.powerset, if (J : Set ι) ⊆ E then (-1 : ℝ)^J.card else 0) =
      if Disjoint (P : Set ι) E then 1 else 0 := by
  classical
  let Q := P.filter (fun p => p ∈ E)
  have hfilter : P.powerset.filter (fun J : Finset ι => (J : Set ι) ⊆ E) = Q.powerset := by
    ext J
    simp only [mem_filter, mem_powerset, Q, subset_iff]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      exact ⟨h1 hj, h2 hj⟩
    · intro h
      exact ⟨fun j hj => (h hj).1, fun j hj => (h hj).2⟩
  rw [← sum_filter, hfilter]
  have hempty : Q = ∅ ↔ Disjoint (P : Set ι) E := by
    simp only [Q, filter_eq_empty_iff, Set.disjoint_left, mem_coe]
  by_cases he : Q = ∅
  · simp [he, hempty.mp he]
  · have hc : Q.card ≠ 0 := Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr he)
    have hp := Finset.prod_sub (fun _ : ι => (1 : ℝ)) (fun _ => 1) Q
    simpa [he, hc, mt hempty.mpr he] using hp.symm

private theorem empty_recovery {ι Ω : Type*} [DecidableEq ι]
    (P : Finset ι) (F : Finset Ω) (w : Ω → ℝ) (E : Ω → Set ι) :
    (∑ J ∈ P.powerset, (-1 : ℝ)^J.card *
      (∑ i ∈ F, if (J : Set ι) ⊆ E i then w i else 0)) =
      ∑ i ∈ F, if Disjoint (P : Set ι) (E i) then w i else 0 := by
  classical
  simp_rw [Finset.mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  calc
    _ = (∑ J ∈ P.powerset, if (J : Set ι) ⊆ E i then (-1 : ℝ)^J.card else 0) * w i := by
      rw [sum_mul]
      refine sum_congr rfl fun J _ => ?_
      by_cases h : (J : Set ι) ⊆ E i <;> simp [h]
    _ = _ := by rw [subset_sign_sum]; split <;> simp

private theorem sign_target {ι : Type*} [DecidableEq ι] (P : Finset ι) (h : ι → ℝ) :
    (∑ J ∈ P.powerset, (-1 : ℝ)^J.card *
      ((if J = ∅ then 1 - ∑ p ∈ P, h p else 0) +
        ∑ p ∈ P, if (J : Set ι) ⊆ {p} then h p else 0)) =
      1 - ∑ p ∈ P, h p := by
  classical
  simp_rw [mul_add, sum_add_distrib]
  have base : (∑ J ∈ P.powerset, (-1 : ℝ)^J.card *
      (if J = ∅ then 1 - ∑ p ∈ P, h p else 0)) = 1 - ∑ p ∈ P, h p := by
    simp [mul_ite]
  rw [base, empty_recovery]
  simp only [add_eq_left]
  refine sum_eq_zero fun p hp => ?_
  have hd : ¬ Disjoint (P : Set ι) ({p} : Set ι) := by
    intro hd
    exact Set.disjoint_left.mp hd hp (Set.mem_singleton p)
  simp [hd]

open MeasureTheory in
private theorem stable_integral {ι Ω : Type*} [DecidableEq ι] [MeasurableSpace Ω]
    (P : Finset ι) (h : ι → ℝ) (μ : Measure Ω) (w : Ω → ℝ) (E : Ω → Set ι)
    (hw : Integrable w μ) (hn : ∫ x, w x ∂μ = 1)
    (hE : ∀ p, MeasurableSet {x | p ∈ E x}) :
    let obs := fun J : Finset ι => ∫ x, (if (J : Set ι) ⊆ E x then w x else 0) ∂μ
    let model := fun J : Finset ι => (if J = ∅ then 1 - ∑ p ∈ P, h p else 0) +
      ∑ p ∈ P, if (J : Set ι) ⊆ {p} then h p else 0
    2 * (∑ p ∈ P, h p) - 1 ≤
      (∫ x, |w x| ∂μ) + 2 * ∑ J ∈ P.powerset, |obs J - model J| := by
  classical
  intro obs model
  let d := fun (J : Finset ι) x => (-1 : ℝ)^J.card * (if (J : Set ι) ⊆ E x then w x else 0)
  have hd (J : Finset ι) : Integrable (d J) μ := by
    refine Integrable.const_mul ?_ _
    have hm : MeasurableSet {x | (J : Set ι) ⊆ E x} := by
      convert! J.measurableSet_biInter (f := fun p => {x | p ∈ E x}) (fun p _ => hE p) using 1
      ext x
      simp
      rfl
    exact hw.indicator hm
  let delta := fun x => ∑ J ∈ P.powerset, d J x
  have hi : Integrable delta μ := integrable_finsetSum _ (fun J _ => hd J)
  have hdelta : ∫ x, delta x ∂μ = ∑ J ∈ P.powerset, (-1 : ℝ)^J.card * obs J := by
    dsimp only [delta]
    rw [integral_finsetSum _ (fun J _ => hd J)]
    exact sum_congr rfl (fun J _ => integral_const_mul _ _)
  have hcost : 1 - 2 * (∫ x, delta x ∂μ) ≤ ∫ x, |w x| ∂μ := by
    rw [← hn, ← integral_const_mul, ← integral_sub hw (hi.const_mul 2)]
    apply integral_mono (hw.sub (hi.const_mul _)) hw.abs
    intro x
    have hx : delta x = (if Disjoint (P : Set ι) (E x) then 1 else 0) * w x := by
      rw [← subset_sign_sum P (E x), sum_mul]
      refine sum_congr rfl fun J _ => ?_
      by_cases hj : (J : Set ι) ⊆ E x <;> simp [d, hj]
    change w x - 2 * delta x ≤ |w x|
    rw [hx]
    split
    · simp only [one_mul]
      linarith [neg_abs_le (w x)]
    · simp [le_abs_self]
  have hdiff : (∫ x, delta x ∂μ) - (1 - ∑ p ∈ P, h p) ≤
      ∑ J ∈ P.powerset, |obs J - model J| := by
    have hmod : (∑ J ∈ P.powerset, (-1 : ℝ)^J.card * model J) = 1 - ∑ p ∈ P, h p :=
      sign_target P h
    rw [hdelta, ← hmod, ← sum_sub_distrib]
    refine sum_le_sum fun J _ => ?_
    rw [← mul_sub]
    exact (le_abs_self _).trans_eq (by simp [abs_mul])
  linarith

private theorem gram_sums_escape :
    Tendsto (fun P : Finset Nat.Primes =>
      ∑ p ∈ P, (p : ℝ) * (Real.log (p : ℝ))^2 / ((p : ℝ) - 1)^2) atTop atTop := by
  classical
  let c : ℝ := (Real.log 2)^2
  have hc : 0 < c := sq_pos_of_pos (Real.log_pos (by norm_num))
  have hlo (p : Nat.Primes) :
      c * (1 / (p : ℝ)) ≤ (p : ℝ) * (Real.log (p : ℝ))^2 / ((p : ℝ) - 1)^2 := by
    have hp : 2 ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
    have hp0 : 0 < (p : ℝ) := by linarith
    have hl : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by norm_num) hp
    have hc' : c ≤ (Real.log (p : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Real.log_nonneg (by norm_num)) hl 2
    have hsq : ((p : ℝ) - 1)^2 ≤ (p : ℝ)^2 := by nlinarith
    have hden : 0 < ((p : ℝ) - 1)^2 := sq_pos_of_pos (by linarith)
    calc
      c * (1 / (p : ℝ)) ≤ (Real.log (p : ℝ))^2 * (1 / (p : ℝ)) :=
        mul_le_mul_of_nonneg_right hc' (by positivity)
      _ = (p : ℝ) * (Real.log (p : ℝ))^2 / (p : ℝ)^2 := by field_simp
      _ ≤ (p : ℝ) * (Real.log (p : ℝ))^2 / ((p : ℝ)-1)^2 :=
        div_le_div_of_nonneg_left (by positivity) hden hsq
  apply tendsto_atTop_atTop_of_monotone
  · apply Finset.sum_mono_set_of_nonneg
    intro p
    exact (mul_nonneg hc.le (by positivity)).trans (hlo p)
  intro b
  by_contra! hb
  apply Nat.Primes.not_summable_one_div
  apply summable_of_sum_le (c := b / c) (fun p => by positivity)
  intro P
  apply (le_div_iff₀ hc).2
  rw [mul_comm, Finset.mul_sum]
  exact (Finset.sum_le_sum fun p _ => hlo p).trans (hb P).le

private theorem attaining {ι : Type*} [DecidableEq ι] (P : Finset ι) (h : ι → ℝ)
    (hh : ∀ p ∈ P, 0 ≤ h p) :
    ∃ (F : Finset (Option ι)) (w : Option ι → ℝ) (E : Option ι → Set ι),
      (∑ i ∈ F, w i) = 1 ∧
      (∀ J : Finset ι, (∑ i ∈ F, if (J : Set ι) ⊆ E i then w i else 0) =
        (if J = ∅ then 1 - ∑ p ∈ P, h p else 0) +
          ∑ p ∈ P, if (J : Set ι) ⊆ {p} then h p else 0) ∧
      (∑ i ∈ F, |w i|) = |1 - ∑ p ∈ P, h p| + ∑ p ∈ P, h p := by
  classical
  let w (i : Option ι) := i.elim (1 - ∑ p ∈ P, h p) h
  let E (i : Option ι) := i.elim (∅ : Set ι) (fun p => {p})
  refine ⟨P.insertNone, w, E, ?_, ?_, ?_⟩
  · simp [Finset.sum_insertNone, w]
  · intro J
    simp [Finset.sum_insertNone, w, E]
  · rw [Finset.sum_insertNone]
    apply congrArg (fun x => |1 - ∑ p ∈ P, h p| + x)
    exact sum_congr rfl fun p hp => abs_of_nonneg (hh p hp)

open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : ℕ → Measure Ω)
    (w : ℕ → Ω → ℝ) (E : ℕ → Ω → Set Nat.Primes)
    (hw : ∀ n, Integrable (w n) (μ n)) (hn : ∀ n, ∫ x, w n x ∂μ n = 1)
    (hE : ∀ n p, MeasurableSet {x | p ∈ E n x}) :
    let h := fun p : Nat.Primes => (p : ℝ) * (Real.log (p : ℝ))^2 / ((p : ℝ)-1)^2
    let W := fun P : Finset Nat.Primes => ∑ p ∈ P, h p
    let obs := fun n (J : Finset Nat.Primes) =>
      ∫ x, (if (J : Set Nat.Primes) ⊆ E n x then w n x else 0) ∂μ n
    let model := fun (P J : Finset Nat.Primes) => (if J = ∅ then 1 - W P else 0) +
      ∑ p ∈ P, if (J : Set Nat.Primes) ⊆ {p} then h p else 0
    (∀ n P, |1 - W P| + W P ≤ (∫ x, |w n x| ∂μ n) +
      2 * ∑ J ∈ P.powerset, |obs n J - model P J|) ∧
    (37 / 20 < h ⟨2, Nat.prime_two⟩ + h ⟨3, Nat.prime_three⟩) ∧
    (∀ P, ∃ (F : Finset (Option Nat.Primes)) (b : Option Nat.Primes → ℝ)
        (A : Option Nat.Primes → Set Nat.Primes),
      (∑ i ∈ F, b i) = 1 ∧
      (∀ J : Finset Nat.Primes, (∑ i ∈ F, if (J : Set Nat.Primes) ⊆ A i then b i else 0) = model P J) ∧
      (∑ i ∈ F, |b i|) = |1 - W P| + W P) ∧
    ((∀ p, Tendsto (fun n => obs n {p}) atTop (𝓝 (h p))) →
      (∀ J, 2 ≤ J.card → Tendsto (fun n => obs n J) atTop (𝓝 0)) →
      Tendsto (fun n => ∫ x, |w n x| ∂μ n) atTop atTop) := by
  classical
  intro h W obs model
  have hfin (n P) : 2 * W P - 1 ≤ (∫ x, |w n x| ∂μ n) +
      2 * ∑ J ∈ P.powerset, |obs n J - model P J| :=
    stable_integral P h (μ n) (w n) (E n) (hw n) (hn n) (hE n)
  refine ⟨?_, ?_, fun P => attaining P h (fun p _ => by dsimp [h]; positivity), ?_⟩
  · intro n P
    by_cases hy : 1 ≤ W P
    · rw [abs_of_nonpos (by linarith : 1 - W P ≤ 0)]
      linarith [hfin n P]
    · rw [abs_of_nonneg (by linarith : 0 ≤ 1 - W P)]
      have hi : 1 ≤ ∫ x, |w n x| ∂μ n := by
        rw [← hn n]
        exact integral_mono (hw n) (hw n).abs (fun x => le_abs_self _)
      have he : 0 ≤ ∑ J ∈ P.powerset, |obs n J - model P J| :=
        sum_nonneg fun _ _ => abs_nonneg _
      linarith
  · have h2 : (0.693 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
    have h3 : (1.098 : ℝ) < Real.log 3 := lt_trans (by norm_num) Real.log_three_gt_d9
    have hh2 := mul_self_lt_mul_self (by norm_num : (0 : ℝ) ≤ 0.693) h2
    have hh3 := mul_self_lt_mul_self (by norm_num : (0 : ℝ) ≤ 1.098) h3
    dsimp only [h]
    norm_num
    nlinarith
  intro hs hm
  have hlim (P J : Finset Nat.Primes) (hJP : J ⊆ P) :
      Tendsto (fun n => obs n J) atTop (𝓝 (model P J)) := by
    by_cases hJ : J = ∅
    · subst J
      have he (n : ℕ) : obs n ∅ = 1 := by simpa [obs] using hn n
      simp [model, W, he]
    by_cases hcard : J.card = 1
    · obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hcard
      have hp : p ∈ P := hJP (by simp)
      simpa [model, hp, Finset.sum_ite_eq] using (hs p)
    · have two : 2 ≤ J.card := by
        have := Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hJ)
        omega
      have hno (p : Nat.Primes) : ¬ (J : Set Nat.Primes) ⊆ {p} := by
        intro hc
        have hh : J ⊆ {p} := fun i hi => Finset.mem_singleton.mpr (hc hi)
        have he := Finset.card_le_card hh
        simp at he
        omega
      simpa only [model, hJ, if_false, hno, sum_const_zero, add_zero] using hm J two
  apply tendsto_atTop.mpr
  intro B
  obtain ⟨P, hp⟩ : ∃ P : Finset Nat.Primes, B + 3 < W P := by
    exact (gram_sums_escape.eventually_gt_atTop (B + 3)).exists
  have herr : Tendsto (fun n => ∑ J ∈ P.powerset, |obs n J - model P J|) atTop (𝓝 0) := by
    have hj (J : Finset Nat.Primes) (hm : J ∈ P.powerset) :
        Tendsto (fun n => |obs n J - model P J|) atTop (𝓝 0) := by
      simpa using ((hlim P J (Finset.mem_powerset.mp hm)).sub (tendsto_const_nhds (x := model P J))).abs
    simpa using tendsto_finsetSum P.powerset hj
  have hW0 : 0 ≤ W P := by
    apply sum_nonneg
    intro p _
    dsimp [h]
    positivity
  filter_upwards [herr.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with n hn'
  linarith [hfin n P]
