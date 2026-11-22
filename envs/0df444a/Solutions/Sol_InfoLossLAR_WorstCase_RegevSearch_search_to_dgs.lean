-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSearch.search_to_dgs
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T13:41:28.509989+00:00
-- url     : https://prove2.me/submissions/8c2a38bf-b5af-4582-a2b9-c8e2d9acb7fb

import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_search_to_single_coefficient_gaussian
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_independent_coefficient_batch_mqpt

set_option autoImplicit false
open scoped BigOperators Classical
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch

namespace SearchPoolEstimate

private def productMass {X : Type*} (w : X → ℝ) {k : ℕ} (v : Fin k → X) : ℝ :=
  ∏ i, w (v i)

private theorem product_nonneg {X : Type*} {w : X → ℝ} (hw : ∀ x, 0 ≤ w x)
    {k : ℕ} (v : Fin k → X) : 0 ≤ productMass w v :=
  Finset.prod_nonneg fun i _ => hw (v i)

private theorem product_sum {X : Type*} {w : X → ℝ} {a : ℝ}
    (hw : ∀ x, 0 ≤ w x) (hs : HasSum w a) (k : ℕ) :
    HasSum (productMass w (k := k)) (a ^ k) := by
  induction k with
  | zero =>
    have hempty : productMass w (k := 0) = fun _ : Fin 0 → X => (1 : ℝ) := by
      funext v
      simp [productMass]
    rw [hempty, pow_zero]
    simpa only [Fintype.sum_unique] using hasSum_fintype (fun _ : Fin 0 → X => (1 : ℝ))
  | succ k ih =>
    have hp := hs.mul ih (hs.summable.mul_of_nonneg ih.summable hw (product_nonneg hw))
    let e := Fin.consEquiv (fun _ : Fin (k + 1) => X)
    have hcomp : (fun x : X × (Fin k → X) => w x.1 * productMass w x.2) =
        productMass w ∘ e := by
      funext x
      simp [e, productMass, Fin.consEquiv, Fin.prod_univ_succ]
    rw [hcomp] at hp
    simpa only [pow_succ, mul_comm] using e.hasSum_iff.mp hp

private theorem overlap_deficit (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (k : ℕ) :
    1 - a^k ≤ (k : ℝ) * (1-a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hbound : a^k ≤ 1 := pow_le_one₀ ha ha1
    rw [pow_succ, Nat.cast_succ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hbound) (sub_nonneg.mpr ha1)]

private theorem masked_sum_le {X : Type*} {f g : X → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ g x) (sf : Summable f) (sg : Summable g)
    (E : X → Prop) :
    let mask (w : X → ℝ) (x : X) := w x * (if E x then 1 else 0)
    0 ≤ (∑' x, mask g x) - (∑' x, mask f x) ∧
      (∑' x, mask g x) - (∑' x, mask f x) ≤ (∑' x, g x) - (∑' x, f x) := by
  intro mask
  have summask {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (sw : Summable w) : Summable (mask w) := by
    refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) sw
    · by_cases h : E x <;> simp [mask, h, hw]
    · by_cases h : E x <;> simp [mask, h, hw]
  have sf' := summask hf sf
  have sg' := summask (fun x => (hf x).trans (hfg x)) sg
  have hm (x : X) : 0 ≤ mask g x - mask f x ∧ mask g x - mask f x ≤ g x - f x := by
    by_cases h : E x <;> simp [mask, h, hfg]
  rw [← sg'.tsum_sub sf', ← sg.tsum_sub sf]
  exact ⟨tsum_nonneg fun x => (hm x).1,
    (sg'.sub sf').tsum_le_tsum (fun x => (hm x).2) (sg.sub sf)⟩

/-- An event on the whole product can lose at most the mass outside the common product measure. -/
theorem pool_event_bound {X : Type*} (p q : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (sp : HasSum p 1) (sq : Summable q) (tq : (∑' x, q x) ≤ 1)
    (k : ℕ) (event : (Fin k → X) → Prop) :
    |(∑' v : Fin k → X, (∏ i, p (v i)) * (if event v then 1 else 0)) -
      (∑' v : Fin k → X, (∏ i, q (v i)) * (if event v then 1 else 0))| ≤
      (k : ℝ) * ∑' x, |p x - q x| := by
  let common (x : X) := min (p x) (q x)
  have hc (x : X) : 0 ≤ common x := le_min (hp x) (hq x)
  have hcp (x : X) : common x ≤ p x := min_le_left ..
  have hcq (x : X) : common x ≤ q x := min_le_right ..
  have sc : Summable common := Summable.of_nonneg_of_le hc hcp sp.summable
  let a := ∑' x, common x
  have ha : 0 ≤ a := tsum_nonneg hc
  have ha1 : a ≤ 1 := (sc.tsum_le_tsum hcp sp.summable).trans_eq sp.tsum_eq
  have hmissing : 1 - a ≤ ∑' x, |p x - q x| := by
    rw [← sp.tsum_eq, ← sp.summable.tsum_sub sc]
    apply (sp.summable.sub sc).tsum_le_tsum _ (sp.summable.sub sq).abs
    intro x
    by_cases h : p x ≤ q x
    · simp [common, min_eq_left h]
    · rw [show common x = q x from min_eq_right (le_of_not_ge h)]
      exact le_abs_self _
  have pc := product_sum hc sc.hasSum k
  have pp := product_sum hp sp k
  have pq := product_sum hq sq.hasSum k
  have lower (w : X → ℝ) (h : ∀ x, common x ≤ w x) (v : Fin k → X) :
      productMass common v ≤ productMass w v :=
    Finset.prod_le_prod (fun i _ => hc (v i)) (fun i _ => h (v i))
  have hP := masked_sum_le (product_nonneg hc) (lower p hcp) pc.summable pp.summable event
  have hQ := masked_sum_le (product_nonneg hc) (lower q hcq) pc.summable pq.summable event
  dsimp only at hP hQ
  have hpow : (∑' x, q x)^k ≤ 1 := pow_le_one₀ (tsum_nonneg hq) tq
  rw [pp.tsum_eq, one_pow, pc.tsum_eq] at hP
  rw [pq.tsum_eq, pc.tsum_eq] at hQ
  change |(∑' v : Fin k → X, productMass p v * _) -
    (∑' v : Fin k → X, productMass q v * _)| ≤ _
  have hd := (overlap_deficit a ha ha1 k).trans (mul_le_mul_of_nonneg_left hmissing (Nat.cast_nonneg _))
  change 1 - (∑' x, common x)^k ≤ _ at hd
  exact abs_le.mpr ⟨by linarith [hP.1,hQ.2], by linarith [hQ.1,hP.2]⟩

/-- Normalizing a nonnegative series gives a summable weight of mass at most one. -/
private theorem normalized_subprob {X : Type*} (f : X → ℝ) :
    Summable (fun x => f x / ∑' y, f y) ∧ (∑' x, f x / ∑' y, f y) ≤ 1 := by
  by_cases hs : Summable f
  · refine ⟨hs.div_const _, ?_⟩
    rw [tsum_div_const]
    by_cases hz : (∑' x, f x) = 0 <;> simp [hz]
  · simp [tsum_eq_zero_of_not_summable hs]

theorem coefficient_subprob {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) :
    (∀ z, 0 ≤ coefficientMass B r z) ∧ Summable (coefficientMass B r) ∧
    (∑' z, coefficientMass B r z) ≤ 1 := by
  let f (z : Fin n → ℤ) := rhoInt r (B.mulVec z)
  have hf (z : Fin n → ℤ) : 0 ≤ f z := (Real.exp_pos _).le
  exact ⟨fun z => div_nonneg (hf z) (tsum_nonneg hf), normalized_subprob f⟩

end SearchPoolEstimate

open InfoLossLAR.WorstCase.RegevSearch
open QAlgorithms.Complexity

theorem solution : ∀ (S : Set ℕ), S.Infinite → (∀ n ∈ S, 1 ≤ n) →
    ∀ (A : MFamily), IsMQPT A → ∀ (samples : Polynomial ℕ) (cutoff : ℕ),
      SearchOn A samples cutoff S →
      ∃ G : MFamily, IsMQPT G ∧ ∃ error : ℕ → ℝ, InfoLossLAR.WorstCase.Negligible error ∧
        ∃ threshold : ℕ, ∀ n ∈ S, threshold ≤ n → DGSAt G n (error n) := by
  intro S hS hpos A hA samples cutoff hsearch
  obtain ⟨H, hH, error, herr, threshold, hsingle⟩ :=
    search_to_single_coefficient_gaussian S hS hpos A hA samples cutoff hsearch
  obtain ⟨G, hG, hbatch⟩ := independent_coefficient_batch_mqpt H hH
  refine ⟨G, hG, error, herr, threshold, ?_⟩
  intro n hn hthreshold B hB r hr hwidth count budget event
  let precision := count * (budget + 1)
  let p (z : Fin n → ℤ) := outputProb H (dgsInput B r 1 precision)
    (fun out => encVec encI z <+: out)
  obtain ⟨hpSum, hpErr⟩ := hsingle n hn hthreshold B hB r hr hwidth precision
  have hp (z : Fin n → ℤ) : 0 ≤ p z := by
    unfold p outputProb
    exact Finset.sum_nonneg fun y _ => by split_ifs <;> positivity
  obtain ⟨hq, sq, tq⟩ := SearchPoolEstimate.coefficient_subprob B r
  have hproduct := SearchPoolEstimate.pool_event_bound p (coefficientMass B r)
    hp hq hpSum sq tq count event
  rw [hbatch n B r count budget hpSum event]
  refine hproduct.trans ((mul_le_mul_of_nonneg_left hpErr (Nat.cast_nonneg count)).trans ?_)
  rw [mul_add]
  refine add_le_add (le_refl _) ?_
  change (count : ℝ) * (1 / ((precision : ℝ) + 1)) ≤ 1 / ((budget : ℝ) + 1)
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  simp [precision]
