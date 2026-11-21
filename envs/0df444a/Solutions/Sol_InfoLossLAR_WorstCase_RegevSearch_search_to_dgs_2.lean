-- Prove2me | solution 2 for InfoLossLAR.WorstCase.RegevSearch.search_to_dgs
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T14:00:54.407873+00:00
-- url     : https://prove2.me/submissions/4935ec23-8859-4497-8100-a838a6f285a5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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
/-- The normalizing series converges on every full-rank integer basis. -/
theorem coefficient_probability {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (r : ℝ) (hr : 0 < r) :
    (∀ z, 0 ≤ coefficientMass B r z) ∧ HasSum (coefficientMass B r) 1 := by
  let c := -Real.pi / r^2
  let g (j : ℤ) := Real.exp (c * (j : ℝ)^2)
  have hc : c < 0 := div_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) (sq_pos_of_pos hr)
  have hnat : Summable (fun j : ℕ => Real.exp (c * (j : ℝ)^2)) :=
    Real.summable_exp_nat_mul_of_ge hc (fun j => by exact_mod_cast Nat.le_self_pow (by decide : 2 ≠ 0) j)
  have hg : Summable g := Summable.of_nat_of_neg (by simpa [g] using hnat) (by simpa [g] using hnat)
  have hind (v : Fin n → ℤ) : rhoInt r v = productMass g v := by
    unfold rhoInt RegevLWE.GaussConv.rho productMass
    rw [EuclideanSpace.real_norm_sq_eq, ← Real.exp_sum]
    congr 1
    simp only [c, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hs : Summable (fun z => rhoInt r (B.mulVec z)) := by
    have h := (product_sum (fun j => (Real.exp_pos _).le) hg.hasSum n).summable.comp_injective
      (Matrix.mulVec_injective_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_iff_ne_zero.mpr hB))
    exact h.congr (fun z => (hind (B.mulVec z)).symm)
  have hp : 0 < ∑' z, rhoInt r (B.mulVec z) :=
    hs.tsum_pos (fun z => (Real.exp_pos _).le) 0 (Real.exp_pos _)
  refine ⟨fun z => div_nonneg (Real.exp_pos _).le hp.le,?_⟩
  have h := hs.hasSum.div_const (∑' z, rhoInt r (B.mulVec z))
  rw [div_self hp.ne'] at h
  exact h

/-- The product of the two distributions' common mass gives an event bound for every pool.
With normalized marginals its deficit is exactly half their L1 distance. -/
theorem pool_overlap_bound {X : Type*} (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) (sp : HasSum p 1) (sq : HasSum q 1)
    (k : ℕ) (event : (Fin k → X) → Prop) :
    let tv := (∑' x, |p x - q x|) / 2
    let err := |(∑' v : Fin k → X, (∏ i, p (v i)) * (if event v then 1 else 0)) -
      (∑' v : Fin k → X, (∏ i, q (v i)) * (if event v then 1 else 0))|
    err ≤ 1 - (1-tv)^k ∧ 1 - (1-tv)^k ≤ (k : ℝ) * tv := by
  intro tv err
  let common (x : X) := min (p x) (q x)
  have hc (x : X) : 0 ≤ common x := le_min (hp x) (hq x)
  have hcp (x : X) : common x ≤ p x := min_le_left ..
  have hcq (x : X) : common x ≤ q x := min_le_right ..
  have sc : Summable common := Summable.of_nonneg_of_le hc hcp sp.summable
  let a := ∑' x, common x
  have ha : 0 ≤ a := tsum_nonneg hc
  have ha1 : a ≤ 1 := (sc.tsum_le_tsum hcp sp.summable).trans_eq sp.tsum_eq
  have same (x : X) : (p x - common x) + (q x - common x) = |p x - q x| := by
    rcases le_total (p x) (q x) with h | h
    · rw [show common x = p x from min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [show common x = q x from min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  have htotal := ((sp.sub sc.hasSum).add (sq.sub sc.hasSum)).tsum_eq
  simp_rw [same] at htotal
  have hv : 1 - tv = a := by dsimp [tv,a]; linarith
  have pc := product_sum hc sc.hasSum k
  have pp := product_sum hp sp k
  have pq := product_sum hq sq k
  have lower (w : X → ℝ) (h : ∀ x, common x ≤ w x) (v : Fin k → X) :
      productMass common v ≤ productMass w v :=
    Finset.prod_le_prod (fun i _ => hc (v i)) (fun i _ => h (v i))
  have hP := masked_sum_le (product_nonneg hc) (lower p hcp) pc.summable pp.summable event
  have hQ := masked_sum_le (product_nonneg hc) (lower q hcq) pc.summable pq.summable event
  dsimp only at hP hQ
  rw [pp.tsum_eq,one_pow,pc.tsum_eq] at hP
  rw [pq.tsum_eq,one_pow,pc.tsum_eq] at hQ
  rw [hv]
  refine ⟨?_,?_⟩
  · change |(∑' v : Fin k → X, productMass p v * _) -
      (∑' v : Fin k → X, productMass q v * _)| ≤ 1 - (∑' x, common x)^k
    exact abs_le.mpr ⟨by linarith [hP.1,hQ.2],by linarith [hQ.1,hP.2]⟩
  · rw [show tv = 1-a by linarith]
    exact overlap_deficit a ha ha1 k

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
  have halfNegligible : Negligible (fun n => error n / 2) := by
    refine ⟨fun n => div_nonneg (herr.1 n) (by norm_num),?_⟩
    intro c hc
    obtain ⟨N,hN⟩ := herr.2 c hc
    exact ⟨N,fun n hn => (show error n / 2 ≤ error n by linarith [herr.1 n]).trans (hN n hn)⟩
  refine ⟨G, hG, fun n => error n / 2, halfNegligible, threshold, ?_⟩
  intro n hn hthreshold B hB r hr hwidth count budget event
  let precision := count * (budget + 1)
  let p (z : Fin n → ℤ) := outputProb H (dgsInput B r 1 precision)
    (fun out => encVec encI z <+: out)
  obtain ⟨hpSum, hpErr⟩ := hsingle n hn hthreshold B hB r hr hwidth precision
  have hp (z : Fin n → ℤ) : 0 ≤ p z := by
    unfold p outputProb
    exact Finset.sum_nonneg fun y _ => by split_ifs <;> positivity
  obtain ⟨hq, hqSum⟩ := SearchPoolEstimate.coefficient_probability B hB (r : ℝ) (by exact_mod_cast hr)
  obtain ⟨hproduct,hlinear⟩ := SearchPoolEstimate.pool_overlap_bound
    p (coefficientMass B r) hp hq hpSum hqSum count event
  rw [hbatch n B r count budget hpSum event]
  refine (hproduct.trans hlinear).trans ?_
  have hnum : (count : ℝ) * (1 / ((precision : ℝ) + 1)) ≤ 1 / ((budget : ℝ) + 1) := by
    rw [mul_one_div,div_le_div_iff₀ (by positivity) (by positivity)]
    simp [precision]
  have h := mul_le_mul_of_nonneg_left hpErr (Nat.cast_nonneg count)
  rw [mul_add] at h
  change (count : ℝ) * ((∑' z, |p z - coefficientMass B r z|) / 2) ≤
    (count : ℝ) * (error n / 2) + 1 / ((budget : ℝ) + 1)
  change (count : ℝ) * (∑' z, |p z - coefficientMass B r z|) ≤
    (count : ℝ) * error n + (count : ℝ) * (1 / ((precision : ℝ) + 1)) at h
  have hhalf : (count : ℝ) * ((∑' z, |p z - coefficientMass B r z|) / 2) ≤
      (count : ℝ) * (error n / 2) + (1 / ((budget : ℝ) + 1)) / 2 := by
    linarith
  exact hhalf.trans (by linarith [show 0 ≤ 1 / ((budget : ℝ) + 1) by positivity])
