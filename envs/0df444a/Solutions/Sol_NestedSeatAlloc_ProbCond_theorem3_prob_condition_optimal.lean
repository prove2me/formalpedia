-- Prove2me | solution 1 for NestedSeatAlloc.ProbCond.theorem3_prob_condition_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T04:27:20.672635+00:00
-- url     : https://prove2.me/submissions/1c0b3f5f-3453-4efb-b925-1bddff4fb9b0

import Mathlib
import Definitions.Def_NestedSeatAlloc_ProbCond_Model

set_option autoImplicit false

namespace NSA537

open MeasureTheory ProbabilityTheory NestedSeatAlloc.ProbCond

/-- seats sold to class `k+1` when `s` seats remain, protection level `q k`, demand `y`. -/
noncomputable def sold (q : ℕ → ℝ) (k : ℕ) (s y : ℝ) : ℝ := if s < q k then 0 else min (s - q k) y

theorem sold_nonneg (q : ℕ → ℝ) (k : ℕ) (s y : ℝ) (hy : 0 ≤ y) : 0 ≤ sold q k s y := by
  unfold sold; split_ifs with h
  · exact le_rfl
  · exact le_min (by linarith [not_lt.mp h]) hy

theorem sold_le_y (q : ℕ → ℝ) (k : ℕ) (s y : ℝ) (hy : 0 ≤ y) : sold q k s y ≤ y := by
  unfold sold; split_ifs with h
  · exact hy
  · exact min_le_right _ _

theorem sold_le_s (q : ℕ → ℝ) (k : ℕ) (s y : ℝ) (hs : 0 ≤ s) (hq : 0 ≤ q k) :
    sold q k s y ≤ s := by
  unfold sold; split_ifs with h
  · exact hs
  · exact (min_le_left _ _).trans (by linarith)

/-- pathwise one-step decomposition of the revenue. -/
theorem revenue_succ (f q x : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hx : 0 ≤ x (k + 1)) :
    revenue f q x (k + 1) s =
      sold q k s (x (k + 1)) * f (k + 1) + revenue f q x k (s - sold q k s (x (k + 1))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  show revenue f q x (j + 2) s = _
  simp only [revenue]
  unfold sold
  by_cases h1 : s < q (j + 1)
  · simp [h1]
  · by_cases h2 : s < q (j + 1) + x (j + 1 + 1)
    · have hm : min (s - q (j + 1)) (x (j + 1 + 1)) = s - q (j + 1) :=
        min_eq_left (by linarith)
      rw [if_neg h1, if_neg h1, if_pos h2, hm, show s - (s - q (j + 1)) = q (j + 1) by ring]
    · have hm : min (s - q (j + 1)) (x (j + 1 + 1)) = x (j + 1 + 1) :=
        min_eq_right (by linarith [not_lt.mp h2])
      rw [if_neg h1, if_neg h1, if_neg h2, hm]

/-- the exchange inequality: under the slope bounds at `P0`, selling `sold' = sold` with level `P0`
is best among all feasible sales `u ∈ [0, min y s]`. -/
theorem exchange (V : ℝ → ℝ) (g P0 s y u : ℝ) (hy : 0 ≤ y) (hP0 : 0 ≤ P0)
    (hu0 : 0 ≤ u) (huy : u ≤ y) (hus : u ≤ s)
    (h1a : ∀ a b, 0 ≤ a → a ≤ b → b ≤ P0 → g * (b - a) ≤ V b - V a)
    (h1b : ∀ a b, P0 ≤ a → a ≤ b → V b - V a ≤ g * (b - a)) :
    u * g + V (s - u) ≤
      (if s < P0 then 0 else min (s - P0) y) * g +
        V (s - (if s < P0 then 0 else min (s - P0) y)) := by
  by_cases hs : s < P0
  · rw [if_pos hs, sub_zero]
    have := h1a (s - u) s (by linarith) (by linarith) hs.le
    linarith
  · rw [if_neg hs]
    have hs' : P0 ≤ s := not_lt.mp hs
    by_cases hy' : s - P0 ≤ y
    · rw [min_eq_left hy']
      have e : s - (s - P0) = P0 := by ring
      rw [e]
      by_cases ht : s - u ≤ P0
      · have := h1a (s - u) P0 (by linarith) ht le_rfl
        linarith
      · have := h1b P0 (s - u) le_rfl (by linarith)
        linarith
    · have hy'' : y < s - P0 := lt_of_not_ge hy'
      rw [min_eq_right hy''.le]
      have := h1b (s - y) (s - u) (by linarith) (by linarith)
      linarith


/-! ### Infrastructure -/

theorem rev_local (f q : ℕ → ℝ) : ∀ (k : ℕ) (x x' : ℕ → ℝ), (∀ i, i ≤ k → x i = x' i) →
    ∀ s, revenue f q x k s = revenue f q x' k s
  | 0, _, _, _, _ => by simp only [revenue]
  | 1, x, x', h, s => by simp only [revenue]; rw [h 1 le_rfl]
  | k + 2, x, x', h, s => by
    have ih := rev_local f q (k + 1) x x' (fun i hi => h i (by omega))
    simp only [revenue, ih, h (k + 2) le_rfl]

theorem meas_rev (f q : ℕ → ℝ) : ∀ k : ℕ,
    Measurable (fun pr : (ℕ → ℝ) × ℝ => revenue f q pr.1 k pr.2)
  | 0 => by simp only [revenue]; exact measurable_const
  | 1 => by
    simp only [revenue]
    exact Measurable.ite (measurableSet_lt measurable_snd ((measurable_pi_apply 1).comp measurable_fst))
      (measurable_const.mul measurable_snd)
      (measurable_const.mul ((measurable_pi_apply 1).comp measurable_fst))
  | k + 2 => by
    have ih := meas_rev f q (k + 1)
    simp only [revenue]
    have hx : Measurable (fun pr : (ℕ → ℝ) × ℝ => pr.1 (k + 2)) :=
      (measurable_pi_apply (k + 2)).comp measurable_fst
    refine Measurable.ite (measurableSet_lt measurable_snd measurable_const) ?_ ?_
    · exact ih
    refine Measurable.ite (measurableSet_lt measurable_snd (measurable_const.add hx)) ?_ ?_
    · exact ((measurable_snd.sub measurable_const).mul measurable_const).add
        (ih.comp (measurable_fst.prodMk measurable_const))
    · exact (hx.mul measurable_const).add (ih.comp (measurable_fst.prodMk (measurable_snd.sub hx)))

theorem meas_sold (q : ℕ → ℝ) (k : ℕ) (s : ℝ) : Measurable (sold q k s) := by
  unfold sold
  split_ifs
  · exact measurable_const
  · exact measurable_const.min measurable_id

theorem rev_bound (f q : ℕ → ℝ) (hq : IsProtectionPolicy q) (k : ℕ) (hk : 1 ≤ k) :
    ∀ x : ℕ → ℝ, (∀ i, 0 ≤ x i) → ∀ t, 0 ≤ t →
      |revenue f q x k t| ≤ (∑ i ∈ Finset.range (k + 1), |f i|) * t := by
  induction k, hk using Nat.le_induction with
  | base =>
    intro x hx t ht
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have e : revenue f q x 1 t = f 1 * min t (x 1) := by
      simp only [revenue]; split_ifs with h
      · rw [min_eq_left h.le]
      · rw [min_eq_right (not_lt.mp h)]
    rw [e, abs_mul, abs_of_nonneg (le_min ht (hx 1))]
    have h1 : min t (x 1) ≤ t := min_le_left _ _
    have h2 : 0 ≤ min t (x 1) := le_min ht (hx 1)
    nlinarith [abs_nonneg (f 0), abs_nonneg (f 1)]
  | succ k hk ih =>
    intro x hx t ht
    rw [revenue_succ f q x k hk t (hx _), Finset.sum_range_succ]
    set u := sold q k t (x (k + 1))
    have hu0 : 0 ≤ u := sold_nonneg q k t _ (hx _)
    have hut : u ≤ t := sold_le_s q k t _ ht (hq k hk)
    have := ih x hx (t - u) (by linarith)
    have hM : 0 ≤ ∑ i ∈ Finset.range (k + 1), |f i| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    calc |u * f (k + 1) + revenue f q x k (t - u)|
        ≤ |u * f (k + 1)| + |revenue f q x k (t - u)| := abs_add_le _ _
      _ ≤ u * |f (k + 1)| + (∑ i ∈ Finset.range (k + 1), |f i|) * (t - u) := by
          rw [abs_mul, abs_of_nonneg hu0]; linarith
      _ ≤ _ := by nlinarith [abs_nonneg (f (k + 1))]

/-- independence Fubini. -/
theorem indep_fubini {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (Z : Ω → (ℕ → ℝ)) (hY : Measurable Y) (hZ : Measurable Z) (hI : IndepFun Y Z P)
    (H : ℝ → (ℕ → ℝ) → ℝ) (hH : Measurable (Function.uncurry H)) (C : ℝ)
    (hC : ∀ y z, |H y z| ≤ C) :
    ∫ ω, H (Y ω) (Z ω) ∂P = ∫ ω, ∫ ω', H (Y ω) (Z ω') ∂P ∂P := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable).1 hI
  have hint : Integrable (Function.uncurry H) ((P.map Y).prod (P.map Z)) :=
    Integrable.of_bound hH.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun pr => by
        simpa [Real.norm_eq_abs, Function.uncurry] using hC pr.1 pr.2)
  calc ∫ ω, H (Y ω) (Z ω) ∂P
      = ∫ pr, Function.uncurry H pr ∂(P.map (fun ω => (Y ω, Z ω))) :=
        (integral_map (hY.prodMk hZ).aemeasurable hH.aestronglyMeasurable).symm
    _ = ∫ pr, Function.uncurry H pr ∂((P.map Y).prod (P.map Z)) := by rw [hmap]
    _ = ∫ y, ∫ z, H y z ∂(P.map Z) ∂(P.map Y) := integral_prod _ hint
    _ = ∫ ω, ∫ z, H (Y ω) z ∂(P.map Z) ∂P :=
        integral_map hY.aemeasurable
          (hH.stronglyMeasurable.integral_prod_right (ν := P.map Z)).aestronglyMeasurable
    _ = ∫ ω, ∫ ω', H (Y ω) (Z ω') ∂P ∂P := by
        congr 1; ext ω
        exact integral_map hZ.aemeasurable
          (hH.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable

theorem indep_fubini_int {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (Z : Ω → (ℕ → ℝ)) (hY : Measurable Y) (hZ : Measurable Z)
    (H : ℝ → (ℕ → ℝ) → ℝ) (hH : Measurable (Function.uncurry H)) (C : ℝ)
    (hC : ∀ y z, |H y z| ≤ C) :
    Integrable (fun ω => ∫ ω', H (Y ω) (Z ω') ∂P) P := by
  have hm : Measurable (Function.uncurry fun y ω' => H y (Z ω')) :=
    hH.comp (measurable_fst.prodMk (hZ.comp measurable_snd))
  refine Integrable.of_bound
    ((hm.stronglyMeasurable.integral_prod_right (ν := P)).comp_measurable hY).aestronglyMeasurable
    C (Filter.Eventually.of_forall fun ω => ?_)
  have := norm_integral_le_of_norm_le_const (μ := P) (f := fun ω' => H (Y ω) (Z ω')) (C := C)
    (Filter.Eventually.of_forall fun ω' => by simpa [Real.norm_eq_abs] using hC _ _)
  simpa [probReal_univ] using this

/-- the restriction of the demand vector to the classes `≤ k`. -/
noncomputable def Zk {Ω : Type*} (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℕ → ℝ :=
  fun i => if h : i ∈ Finset.range (k + 1) then X i ω else 0

theorem Zk_meas {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (k : ℕ) : Measurable (Zk X k) := by
  refine measurable_pi_lambda _ fun i => ?_
  unfold Zk
  by_cases h : i ∈ Finset.range (k + 1)
  · simp only [h, dif_pos]; exact hX i
  · simp only [h, dif_neg, not_false_eq_true]; exact measurable_const

theorem Zk_eq {Ω : Type*} (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) (i : ℕ) (hi : i ≤ k) :
    Zk X k ω i = X i ω := by
  unfold Zk; rw [dif_pos (Finset.mem_range.mpr (by omega))]

theorem Zk_nonneg {Ω : Type*} (X : ℕ → Ω → ℝ) (hX : ∀ i ω, 0 ≤ X i ω) (k : ℕ) (ω : Ω) (i : ℕ) :
    0 ≤ Zk X k ω i := by
  unfold Zk; split_ifs
  · exact hX i ω
  · exact le_rfl

theorem Zk_indep {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hI : iIndepFun X P) (k : ℕ) :
    IndepFun (X (k + 1)) (Zk X k) P := by
  have h := hI.indepFun_finset {k + 1} (Finset.range (k + 1))
    (Finset.disjoint_singleton_left.mpr (by simp)) hX
  have hφ : Measurable (fun w : ({k + 1} : Finset ℕ) → ℝ => w ⟨k + 1, by simp⟩) :=
    measurable_pi_apply _
  have hψ : Measurable (fun (w : (Finset.range (k + 1)) → ℝ) (i : ℕ) =>
      if h : i ∈ Finset.range (k + 1) then w ⟨i, h⟩ else 0) := by
    refine measurable_pi_lambda _ fun i => ?_
    by_cases h : i ∈ Finset.range (k + 1)
    · simp only [h, dif_pos]; exact measurable_pi_apply _
    · simp only [h, dif_neg, not_false_eq_true]; exact measurable_const
  exact h.comp hφ hψ

/-- child 2: one-step decomposition of the expected revenue. -/
theorem child2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ) (hM : IsSeatModel P X f) (q : ℕ → ℝ)
    (hq : IsProtectionPolicy q) (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun ω => sold q k s (X (k + 1) ω) * f (k + 1) +
        expRevenue P X f q k (s - sold q k s (X (k + 1) ω))) P ∧
      expRevenue P X f q (k + 1) s = ∫ ω, (sold q k s (X (k + 1) ω) * f (k + 1) +
        expRevenue P X f q k (s - sold q k s (X (k + 1) ω))) ∂P := by
  haveI := hM.isProb
  set H : ℝ → (ℕ → ℝ) → ℝ := fun y z => sold q k s (max y 0) * f (k + 1) +
    revenue f q (fun i => max (z i) 0) k (s - sold q k s (max y 0)) with hHdef
  have hH : Measurable (Function.uncurry H) := by
    have h1 : Measurable (fun pr : ℝ × (ℕ → ℝ) => sold q k s (max pr.1 0)) :=
      (meas_sold q k s).comp (measurable_fst.max measurable_const)
    have h2 : Measurable (fun pr : ℝ × (ℕ → ℝ) => fun i => max (pr.2 i) 0) :=
      measurable_pi_lambda _ fun i => ((measurable_pi_apply i).comp measurable_snd).max
        measurable_const
    exact (h1.mul measurable_const).add ((meas_rev f q k).comp (h2.prodMk (measurable_const.sub h1)))
  set C := |f (k + 1)| * s + (∑ i ∈ Finset.range (k + 1), |f i|) * s
  have hC : ∀ y z, |H y z| ≤ C := by
    intro y z
    have hy : 0 ≤ max y 0 := le_max_right _ _
    have hu0 := sold_nonneg q k s _ hy
    have hus := sold_le_s q k s (max y 0) hs (hq k hk)
    have hb := rev_bound f q hq k hk (fun i => max (z i) 0) (fun i => le_max_right _ _)
      (s - sold q k s (max y 0)) (by linarith)
    have hM0 : 0 ≤ ∑ i ∈ Finset.range (k + 1), |f i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    simp only [hHdef]
    calc _ ≤ |sold q k s (max y 0) * f (k + 1)| + |revenue f q (fun i => max (z i) 0) k
            (s - sold q k s (max y 0))| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul, abs_of_nonneg hu0]
        nlinarith [abs_nonneg (f (k + 1))]
  have hY := hM.meas (k + 1)
  have hZ := Zk_meas X hM.meas k
  -- pathwise identities
  have hpath : ∀ ω, revenue f q (fun i => X i ω) (k + 1) s = H (X (k + 1) ω) (Zk X k ω) := by
    intro ω
    rw [revenue_succ f q _ k hk s (hM.nonneg _ ω)]
    simp only [hHdef, max_eq_left (hM.nonneg (k + 1) ω)]
    congr 1
    exact rev_local f q k _ _ (fun i hi => by
      simp only [Zk_eq X k ω i hi, max_eq_left (hM.nonneg i ω)]) _
  have hinner : ∀ y, ∫ ω', H y (Zk X k ω') ∂P =
      sold q k s (max y 0) * f (k + 1) + expRevenue P X f q k (s - sold q k s (max y 0)) := by
    intro y
    have hi : Integrable (fun ω' => revenue f q (fun i => max (Zk X k ω' i) 0) k
        (s - sold q k s (max y 0))) P := by
      have hy : 0 ≤ max y 0 := le_max_right _ _
      refine Integrable.of_bound (C := (∑ i ∈ Finset.range (k + 1), |f i|) *
        (s - sold q k s (max y 0))) ?_ (Filter.Eventually.of_forall fun ω' => ?_)
      · exact ((meas_rev f q k).comp ((measurable_pi_lambda _ fun i =>
          ((measurable_pi_apply i).comp hZ).max measurable_const).prodMk
          measurable_const)).aestronglyMeasurable
      · simpa [Real.norm_eq_abs] using rev_bound f q hq k hk _ (fun i => le_max_right _ _) _
          (by linarith [sold_le_s q k s (max y 0) hs (hq k hk)])
    simp only [hHdef]
    rw [integral_add (integrable_const _) hi, integral_const, probReal_univ, one_smul]
    congr 1
    unfold expRevenue
    congr 1; ext ω'
    exact rev_local f q k _ _ (fun i hi => by
      simp only [Zk_eq X k ω' i hi, max_eq_left (hM.nonneg i ω')]) _
  have hfun : (fun ω => sold q k s (X (k + 1) ω) * f (k + 1) +
      expRevenue P X f q k (s - sold q k s (X (k + 1) ω))) =
      fun ω => ∫ ω', H (X (k + 1) ω) (Zk X k ω') ∂P := by
    ext ω; rw [hinner, max_eq_left (hM.nonneg (k + 1) ω)]
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact indep_fubini_int P _ _ hY hZ H hH C hC
  · rw [hfun]
    unfold expRevenue
    simp only [hpath]
    exact indep_fubini P _ _ hY hZ (Zk_indep P X hM.meas hM.indep k) H hH C hC


/-! ### Child 1: slope bounds under (31) -/

theorem minmin (a b S : ℝ) (hab : a ≤ b) :
    0 ≤ min b S - min a S ∧ min b S - min a S ≤ b - a := by
  have h1 : min a S ≤ min b S := min_le_min hab le_rfl
  refine ⟨by linarith, ?_⟩
  rcases le_total a S with h | h
  · rw [min_eq_left h]; linarith [min_le_left b S]
  · rw [min_eq_right h]; linarith [min_le_right b S]

theorem int_minmin {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Set Ω) (hN : MeasurableSet N) (S : Ω → ℝ) (hS : Measurable S) (a b : ℝ) (hab : a ≤ b) :
    Integrable (N.indicator fun ω => min b (S ω) - min a (S ω)) P := by
  refine Integrable.indicator (Integrable.of_bound (C := b - a)
    ((measurable_const.min hS).sub (measurable_const.min hS)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)) hN
  have := minmin a b (S ω) hab
  rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2

theorem bounds_of_E {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Set Ω) (hN : MeasurableSet N) (S : Ω → ℝ) (hS : Measurable S) (V : ℝ → ℝ)
    (f1 L P1 : ℝ) (hf1 : 0 ≤ f1)
    (hE : ∀ a b, L ≤ a → a ≤ b →
      V b - V a = f1 * ∫ ω, N.indicator (fun ω => min b (S ω) - min a (S ω)) ω ∂P) :
    (∀ a b, L ≤ a → a ≤ b → b ≤ P1 →
      f1 * P.real (N ∩ {ω | P1 < S ω}) * (b - a) ≤ V b - V a) ∧
    (∀ a b, L ≤ a → P1 ≤ a → a ≤ b →
      V b - V a ≤ f1 * P.real (N ∩ {ω | P1 < S ω}) * (b - a)) := by
  have hNS : MeasurableSet (N ∩ {ω | P1 < S ω}) := hN.inter (measurableSet_lt measurable_const hS)
  constructor
  · intro a b ha hab hb
    rw [hE a b ha hab, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hf1
    rw [← smul_eq_mul, ← integral_indicator_const _ hNS]
    apply integral_mono ((integrable_const (b - a)).indicator hNS) (int_minmin P N hN S hS a b hab)
    intro ω
    have hmm := minmin a b (S ω) hab
    by_cases hω : ω ∈ N
    · by_cases hs : P1 < S ω
      · rw [Set.indicator_of_mem (show ω ∈ N ∩ {ω | P1 < S ω} from ⟨hω, hs⟩),
          Set.indicator_of_mem hω, min_eq_left (by linarith), min_eq_left (by linarith)]
      · rw [Set.indicator_of_notMem (fun h => hs h.2), Set.indicator_of_mem hω]; exact hmm.1
    · rw [Set.indicator_of_notMem (fun h => hω h.1), Set.indicator_of_notMem hω]
  · intro a b ha hPa hab
    rw [hE a b ha hab, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hf1
    rw [← smul_eq_mul, ← integral_indicator_const _ hNS]
    apply integral_mono (int_minmin P N hN S hS a b hab) ((integrable_const (b - a)).indicator hNS)
    intro ω
    have hmm := minmin a b (S ω) hab
    by_cases hω : ω ∈ N
    · by_cases hs : P1 < S ω
      · rw [Set.indicator_of_mem (show ω ∈ N ∩ {ω | P1 < S ω} from ⟨hω, hs⟩),
          Set.indicator_of_mem hω]; exact hmm.2
      · rw [Set.indicator_of_notMem (s := N ∩ {ω | P1 < S ω}) (fun h => hs h.2),
          Set.indicator_of_mem hω, min_eq_right (show S ω ≤ b by linarith [not_lt.mp hs]),
          min_eq_right (show S ω ≤ a by linarith [not_lt.mp hs])]; simp
    · rw [Set.indicator_of_notMem hω]
      by_cases h : ω ∈ N ∩ {ω | P1 < S ω}
      · rw [Set.indicator_of_mem h]; linarith
      · rw [Set.indicator_of_notMem h]

theorem nest_meas {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (p : ℕ → ℝ) (k : ℕ) : MeasurableSet (nestEvent X p k) := by
  have : nestEvent X p k =
      ⋂ j ∈ Finset.Icc 1 k, {ω | p j < ∑ i ∈ Finset.Icc 1 j, X i ω} := by
    ext ω; simp [nestEvent]
  rw [this]
  exact Finset.measurableSet_biInter _ fun j _ =>
    measurableSet_lt measurable_const (Finset.measurable_sum _ fun i _ => hX i)

theorem nest_succ {Ω : Type*} (X : ℕ → Ω → ℝ) (p : ℕ → ℝ) (k : ℕ) :
    nestEvent X p k ∩ {ω | p (k + 1) < ∑ i ∈ Finset.Icc 1 (k + 1), X i ω} =
      nestEvent X p (k + 1) := by
  ext ω
  simp only [nestEvent, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩ j ⟨hj1, hj2⟩
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · exact h1 j ⟨hj1, by omega⟩
    · obtain rfl : j = k + 1 := by omega
      exact h2
  · intro h
    exact ⟨fun j hj => h j ⟨hj.1, by omega⟩, h (k + 1) ⟨by omega, le_rfl⟩⟩

theorem f1_pos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f) (h31 : ProbCondition P X f p) :
    0 < f 1 := by
  haveI := hM.isProb
  have h := h31 1 le_rfl
  have hlt := hM.fare_strictAnti 1 le_rfl
  have hle : P.real (nestEvent X p 1) ≤ 1 := measureReal_le_one
  have hge : 0 ≤ P.real (nestEvent X p 1) := measureReal_nonneg
  by_contra hneg
  push_neg at hneg
  nlinarith

theorem p_mono {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f) (h31 : ProbCondition P X f p)
    (k : ℕ) (hk : 1 ≤ k) : p k ≤ p (k + 1) := by
  by_contra hlt
  push_neg at hlt
  have hset : nestEvent X p (k + 1) = nestEvent X p k := by
    rw [← nest_succ]
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_iff_left_iff_imp]
    intro hω
    have hk' := hω k (Finset.mem_Icc.mpr ⟨hk, le_rfl⟩)
    rw [Finset.sum_Icc_succ_top (by omega)]
    linarith [hM.nonneg (k + 1) ω]
  have e1 := h31 k hk
  have e2 := h31 (k + 1) (by omega)
  rw [hset, e1] at e2
  linarith [hM.fare_strictAnti (k + 1) (by omega)]

/-- below the protection level the extra class sells nothing. -/
theorem er_succ_below {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f) (k : ℕ) (hk : 1 ≤ k) (t : ℝ)
    (ht : t ≤ p k) : expRevenue P X f p (k + 1) t = expRevenue P X f p k t := by
  unfold expRevenue
  congr 1; ext ω
  rw [revenue_succ f p _ k hk t (hM.nonneg _ ω)]
  have : sold p k t (X (k + 1) ω) = 0 := by
    unfold sold; split_ifs with h
    · rfl
    · rw [show t - p k = 0 by linarith [not_lt.mp h]]
      exact min_eq_left (hM.nonneg _ ω)
  rw [this]; simp

/-- level-1 clipped-difference formula. -/
theorem E_base {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    expRevenue P X f p (0 + 1) b - expRevenue P X f p (0 + 1) a =
      f 1 * ∫ ω, (nestEvent X p 0).indicator (fun ω => min b (∑ i ∈ Finset.Icc 1 (0 + 1), X i ω) -
        min a (∑ i ∈ Finset.Icc 1 (0 + 1), X i ω)) ω ∂P := by
  haveI := hM.isProb
  have hn : nestEvent X p 0 = Set.univ := by ext ω; simp [nestEvent]
  rw [hn, Set.indicator_univ]
  simp only [zero_add, Finset.Icc_self, Finset.sum_singleton]
  have e : ∀ s, expRevenue P X f p 1 s = ∫ ω, f 1 * min s (X 1 ω) ∂P := by
    intro s; unfold expRevenue; congr 1; ext ω
    simp only [revenue]; split_ifs with h
    · rw [min_eq_left h.le]
    · rw [min_eq_right (not_lt.mp h)]
  have hint : ∀ s, 0 ≤ s → Integrable (fun ω => min s (X 1 ω)) P := by
    intro s hs
    refine Integrable.of_bound (C := s) (measurable_const.min (hM.meas 1)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hs (hM.nonneg 1 ω))]; exact min_le_left _ _
  rw [e, e, integral_const_mul, integral_const_mul, ← mul_sub,
    ← integral_sub (hint b (ha.trans hab)) (hint a ha)]


theorem id_min (P c y S : ℝ) (hc : P ≤ c) (hS : P < S) (hy : 0 ≤ y) :
    min (c - P) y + min (max P (c - y)) S = min c (S + y) := by
  rcases le_total (c - P) y with h | h <;> rcases le_total (c - y) S with h' | h' <;>
    simp only [min_def, max_def] <;> split_ifs <;> linarith

theorem sold_ge (q : ℕ → ℝ) (k : ℕ) (s y : ℝ) (hs : q k ≤ s) :
    sold q k s y = min (s - q k) y := by
  unfold sold; rw [if_neg (not_lt.mpr hs)]

theorem sub_min_eq (P s y : ℝ) : s - min (s - P) y = max P (s - y) := by
  rcases le_total (s - P) y with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]; ring
  · rw [min_eq_right h, max_eq_right (by linarith)]

theorem Zk_sum {Ω : Type*} (X : ℕ → Ω → ℝ) (K : ℕ) (ω : Ω) (j : ℕ) (hj : j ≤ K) :
    ∑ i ∈ Finset.Icc 1 j, Zk X K ω i = ∑ i ∈ Finset.Icc 1 j, X i ω :=
  Finset.sum_congr rfl fun i hi => Zk_eq X K ω i (by simp at hi; omega)

theorem Zk_mem {Ω : Type*} (X : ℕ → Ω → ℝ) (p : ℕ → ℝ) (K : ℕ) (ω : Ω) :
    Zk X K ω ∈ {z : ℕ → ℝ | ∀ j ∈ Finset.Icc 1 K, p j < ∑ i ∈ Finset.Icc 1 j, z i} ↔
      ω ∈ nestEvent X p K := by
  simp only [Set.mem_setOf_eq, nestEvent]
  constructor
  · intro h j hj; rw [← Zk_sum X K ω j (by simp at hj; omega)]; exact h j hj
  · intro h j hj; rw [Zk_sum X K ω j (by simp at hj; omega)]; exact h j hj

open Classical in
/-- inductive step of the clipped-difference formula. -/
theorem E_step {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (h31 : ProbCondition P X f p) (k : ℕ) (L : ℝ) (hL : L ≤ p (k + 1))
    (hE : ∀ a b, L ≤ a → a ≤ b →
      expRevenue P X f p (k + 1) b - expRevenue P X f p (k + 1) a =
        f 1 * ∫ ω, (nestEvent X p k).indicator (fun ω => min b (∑ i ∈ Finset.Icc 1 (k + 1), X i ω) -
          min a (∑ i ∈ Finset.Icc 1 (k + 1), X i ω)) ω ∂P) :
    ∀ a b, p (k + 1) ≤ a → a ≤ b →
      expRevenue P X f p (k + 1 + 1) b - expRevenue P X f p (k + 1 + 1) a =
        f 1 * ∫ ω, (nestEvent X p (k + 1)).indicator
          (fun ω => min b (∑ i ∈ Finset.Icc 1 (k + 1 + 1), X i ω) -
            min a (∑ i ∈ Finset.Icc 1 (k + 1 + 1), X i ω)) ω ∂P := by
  haveI := hM.isProb
  intro a b ha hab
  have hP0 : 0 ≤ p (k + 1) := hp _ (by omega)
  obtain ⟨hib, eb⟩ := child2 P X f hM p hp (k + 1) (by omega) b (by linarith)
  obtain ⟨hia, ea⟩ := child2 P X f hM p hp (k + 1) (by omega) a (by linarith)
  rw [eb, ea, ← integral_sub hib hia]
  set S : Ω → ℝ := fun ω => ∑ i ∈ Finset.Icc 1 (k + 1), X i ω with hSdef
  have hS : Measurable S := Finset.measurable_sum _ fun i _ => hM.meas i
  set nz : Set (ℕ → ℝ) := {z : ℕ → ℝ | ∀ j ∈ Finset.Icc 1 (k + 1), p j < ∑ i ∈ Finset.Icc 1 j, z i}
    with hnz
  have hnzm : MeasurableSet nz := by
    have : nz = ⋂ j ∈ Finset.Icc 1 (k + 1), {z : ℕ → ℝ | p j < ∑ i ∈ Finset.Icc 1 j, z i} := by
      ext z; simp [hnz]
    rw [this]
    exact Finset.measurableSet_biInter _ fun j _ =>
      measurableSet_lt measurable_const (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
  set H : ℝ → (ℕ → ℝ) → ℝ := fun y z => if z ∈ nz then
    min b (∑ i ∈ Finset.Icc 1 (k + 1), z i + y) - min a (∑ i ∈ Finset.Icc 1 (k + 1), z i + y)
    else 0 with hHdef
  have hH : Measurable (Function.uncurry H) := by
    have hsz : Measurable (fun pr : ℝ × (ℕ → ℝ) => ∑ i ∈ Finset.Icc 1 (k + 1), pr.2 i + pr.1) :=
      (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp measurable_snd).add
        measurable_fst
    exact Measurable.ite (measurable_snd hnzm)
      ((measurable_const.min hsz).sub (measurable_const.min hsz)) measurable_const
  have hC : ∀ y z, |H y z| ≤ b - a := by
    intro y z
    simp only [hHdef]
    split_ifs
    · have := minmin a b (∑ i ∈ Finset.Icc 1 (k + 1), z i + y) hab
      rw [abs_of_nonneg this.1]; exact this.2
    · simp; linarith
  have hY := hM.meas (k + 1 + 1)
  have hZ := Zk_meas X hM.meas (k + 1)
  have hN := nest_meas X hM.meas p k
  have hN' := nest_meas X hM.meas p (k + 1)
  -- pointwise identity for each outer ω
  have hpt : ∀ ω, (sold p (k + 1) b (X (k + 1 + 1) ω) * f (k + 1 + 1) +
      expRevenue P X f p (k + 1) (b - sold p (k + 1) b (X (k + 1 + 1) ω))) -
      (sold p (k + 1) a (X (k + 1 + 1) ω) * f (k + 1 + 1) +
      expRevenue P X f p (k + 1) (a - sold p (k + 1) a (X (k + 1 + 1) ω))) =
      f 1 * ∫ ω', H (X (k + 1 + 1) ω) (Zk X (k + 1) ω') ∂P := by
    intro ω
    set y := X (k + 1 + 1) ω
    have hy : 0 ≤ y := hM.nonneg _ ω
    rw [sold_ge p (k + 1) b y (by linarith), sold_ge p (k + 1) a y ha,
      sub_min_eq, sub_min_eq]
    set ta := max (p (k + 1)) (a - y)
    set tb := max (p (k + 1)) (b - y)
    have hta : L ≤ ta := hL.trans (le_max_left _ _)
    have htab : ta ≤ tb := max_le_max le_rfl (by linarith)
    have hEt := hE ta tb hta htab
    set c := min (b - p (k + 1)) y - min (a - p (k + 1)) y
    have hf := h31 (k + 1) (by omega)
    have hsplit : ∫ ω', H y (Zk X (k + 1) ω') ∂P =
        ∫ ω', ((nestEvent X p (k + 1)).indicator (fun _ => c) ω' +
          (nestEvent X p k).indicator (fun ω' => min tb (S ω') - min ta (S ω')) ω') ∂P := by
      congr 1; ext ω'
      have hm := Zk_mem X p (k + 1) ω'
      have hsum := Zk_sum X (k + 1) ω' (k + 1) le_rfl
      simp only [hHdef]
      by_cases h1 : ω' ∈ nestEvent X p (k + 1)
      · have h1' : ω' ∈ nestEvent X p k ∧ p (k + 1) < S ω' := by
          rw [← nest_succ] at h1; exact h1
        rw [if_pos (hm.mpr h1), Set.indicator_of_mem h1, Set.indicator_of_mem h1'.1, hsum]
        have e1 := id_min (p (k + 1)) b y (S ω') (ha.trans hab) h1'.2 hy
        have e2 := id_min (p (k + 1)) a y (S ω') ha h1'.2 hy
        simp only [hSdef] at e1 e2 ⊢
        linarith
      · rw [if_neg (fun h => h1 (hm.mp h)), Set.indicator_of_notMem h1]
        by_cases h2 : ω' ∈ nestEvent X p k
        · rw [Set.indicator_of_mem h2]
          have hle : S ω' ≤ p (k + 1) := by
            by_contra hc; push_neg at hc
            exact h1 (by rw [← nest_succ]; exact ⟨h2, hc⟩)
          rw [min_eq_right (hle.trans (le_max_left _ _)),
            min_eq_right (hle.trans (le_max_left _ _))]
          ring
        · rw [Set.indicator_of_notMem h2]; ring
    have hEt' : expRevenue P X f p (k + 1) tb - expRevenue P X f p (k + 1) ta =
        f 1 * ∫ ω', (nestEvent X p k).indicator (fun ω' => min tb (S ω') - min ta (S ω')) ω' ∂P :=
      hEt
    rw [hsplit, integral_add ((integrable_const c).indicator hN')
      (int_minmin P _ hN S hS ta tb htab), integral_indicator_const _ hN']
    simp only [smul_eq_mul]
    rw [mul_add, ← hEt', ← hf]
    ring
  have hfun := funext hpt
  rw [hfun, integral_const_mul,
    ← indep_fubini P _ _ hY hZ (Zk_indep P X hM.meas hM.indep (k + 1)) H hH (b - a) hC]
  congr 1
  congr 1; ext ω
  have hm := Zk_mem X p (k + 1) ω
  have hsum := Zk_sum X (k + 1) ω (k + 1) le_rfl
  simp only [hHdef]
  by_cases h1 : ω ∈ nestEvent X p (k + 1)
  · rw [if_pos (hm.mpr h1), Set.indicator_of_mem h1, hsum]
    simp only [Finset.sum_Icc_succ_top (show 1 ≤ k + 1 + 1 by omega)]
  · rw [if_neg (fun h => h1 (hm.mp h)), Set.indicator_of_notMem h1]


theorem E_all {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (h31 : ProbCondition P X f p) : ∀ k : ℕ, ∀ a b, p (k + 1) ≤ a → a ≤ b →
      expRevenue P X f p (k + 1 + 1) b - expRevenue P X f p (k + 1 + 1) a =
        f 1 * ∫ ω, (nestEvent X p (k + 1)).indicator
          (fun ω => min b (∑ i ∈ Finset.Icc 1 (k + 1 + 1), X i ω) -
            min a (∑ i ∈ Finset.Icc 1 (k + 1 + 1), X i ω)) ω ∂P := by
  intro k
  induction k with
  | zero =>
    exact E_step P X f p hM hp h31 0 0 (hp 1 le_rfl)
      (fun a b ha hab => E_base P X f p hM a b ha hab)
  | succ k ih =>
    exact E_step P X f p hM hp h31 (k + 1) (p (k + 1)) (p_mono P X f p hM h31 (k + 1) (by omega)) ih

theorem child1_all {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (h31 : ProbCondition P X f p) : ∀ k : ℕ,
      (∀ a b, 0 ≤ a → a ≤ b → b ≤ p (k + 1) →
        f (k + 1 + 1) * (b - a) ≤ expRevenue P X f p (k + 1) b - expRevenue P X f p (k + 1) a) ∧
      (∀ a b, p (k + 1) ≤ a → a ≤ b →
        expRevenue P X f p (k + 1) b - expRevenue P X f p (k + 1) a ≤ f (k + 1 + 1) * (b - a)) := by
  haveI := hM.isProb
  have hf1 := f1_pos P X f p hM h31
  intro k
  induction k with
  | zero =>
    have hb := bounds_of_E P (nestEvent X p 0) (nest_meas X hM.meas p 0)
      (fun ω => ∑ i ∈ Finset.Icc 1 (0 + 1), X i ω)
      (Finset.measurable_sum _ fun i _ => hM.meas i) (expRevenue P X f p (0 + 1)) (f 1) 0 (p (0 + 1))
      hf1.le (fun a b ha hab => E_base P X f p hM a b ha hab)
    beta_reduce at hb
    rw [nest_succ, h31 (0 + 1) (by omega)] at hb
    exact ⟨fun a b ha hab hbP => hb.1 a b ha hab hbP,
      fun a b hPa hab => hb.2 a b ((hp 1 le_rfl).trans hPa) hPa hab⟩
  | succ k ih =>
    have hb := bounds_of_E P (nestEvent X p (k + 1)) (nest_meas X hM.meas p (k + 1))
      (fun ω => ∑ i ∈ Finset.Icc 1 (k + 1 + 1), X i ω)
      (Finset.measurable_sum _ fun i _ => hM.meas i) (expRevenue P X f p (k + 1 + 1)) (f 1)
      (p (k + 1)) (p (k + 1 + 1)) hf1.le (E_all P X f p hM hp h31 k)
    beta_reduce at hb
    rw [nest_succ, h31 (k + 1 + 1) (by omega)] at hb
    have hmono := p_mono P X f p hM h31 (k + 1) (by omega)
    refine ⟨?_, fun a b hPa hab => hb.2 a b (hmono.trans hPa) hPa hab⟩
    intro a b ha hab hbP
    have hfl : f (k + 1 + 1 + 1) < f (k + 1 + 1) := hM.fare_strictAnti (k + 1 + 1) (by omega)
    have below : ∀ t, t ≤ p (k + 1) →
        expRevenue P X f p (k + 1 + 1) t = expRevenue P X f p (k + 1) t :=
      fun t ht => er_succ_below P X f p hM (k + 1) (by omega) t ht
    rcases le_total (p (k + 1)) a with h1 | h1
    · exact hb.1 a b h1 hab hbP
    · rcases le_total b (p (k + 1)) with h2 | h2
      · rw [below b h2, below a h1]
        have := ih.1 a b ha hab h2
        have := mul_le_mul_of_nonneg_right hfl.le (sub_nonneg.mpr hab)
        linarith
      · have e1 := hb.1 (p (k + 1)) b le_rfl h2 hbP
        have e2 := ih.1 a (p (k + 1)) ha h1 le_rfl
        rw [below (p (k + 1)) le_rfl] at e1
        rw [below a h1]
        have := mul_le_mul_of_nonneg_right hfl.le (sub_nonneg.mpr h1)
        nlinarith

/-- Assembly: the parent follows from the slope bounds (child 1) and the one-step
independence decomposition (child 2). -/
theorem assembly {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (child1 : ∀ k, 1 ≤ k →
      (∀ a b, 0 ≤ a → a ≤ b → b ≤ p k →
        f (k + 1) * (b - a) ≤ expRevenue P X f p k b - expRevenue P X f p k a) ∧
      (∀ a b, p k ≤ a → a ≤ b →
        expRevenue P X f p k b - expRevenue P X f p k a ≤ f (k + 1) * (b - a)))
    (child2 : ∀ q, IsProtectionPolicy q → ∀ k, 1 ≤ k → ∀ s, 0 ≤ s →
      Integrable (fun ω => sold q k s (X (k + 1) ω) * f (k + 1) +
        expRevenue P X f q k (s - sold q k s (X (k + 1) ω))) P ∧
      expRevenue P X f q (k + 1) s = ∫ ω, (sold q k s (X (k + 1) ω) * f (k + 1) +
        expRevenue P X f q k (s - sold q k s (X (k + 1) ω))) ∂P) :
    IsOptimal P X f p := by
  intro q hq k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro s _
    apply le_of_eq
    simp only [expRevenue, revenue]
  | succ k hk ih =>
    intro s hs
    obtain ⟨hiq, heq⟩ := child2 q hq k hk s hs
    obtain ⟨hip, hep⟩ := child2 p hp k hk s hs
    rw [heq, hep]
    apply integral_mono hiq hip
    intro ω
    have hy := hM.nonneg (k + 1) ω
    have h0 := sold_nonneg q k s (X (k + 1) ω) hy
    have h1 := sold_le_s q k s (X (k + 1) ω) hs (hq k hk)
    calc sold q k s (X (k + 1) ω) * f (k + 1) +
          expRevenue P X f q k (s - sold q k s (X (k + 1) ω))
        ≤ sold q k s (X (k + 1) ω) * f (k + 1) +
          expRevenue P X f p k (s - sold q k s (X (k + 1) ω)) := by
          gcongr; exact ih _ (by linarith)
      _ ≤ _ := by
          have := exchange (expRevenue P X f p k) (f (k + 1)) (p k) s (X (k + 1) ω)
            (sold q k s (X (k + 1) ω)) hy (hp k hk) h0 (sold_le_y q k s _ hy) h1
            (child1 k hk).1 (child1 k hk).2
          simpa only [sold] using this

end NSA537

open MeasureTheory ProbabilityTheory NestedSeatAlloc.ProbCond in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (h31 : ProbCondition P X f p) :
    IsOptimal P X f p := by
  refine NSA537.assembly P X f p hM hp (fun K hK => ?_)
    (fun q hq k hk s hs => NSA537.child2 P X f hM q hq k hk s hs)
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  exact NSA537.child1_all P X f p hM hp h31 k
