-- Prove2me | solution 1 for LinearChoresCLS.lemma_7_5
-- status  : ACCEPTED   (prove)
-- author  : @Weiqiang
-- created : 2026-11-13T20:32:21.705376+00:00
-- url     : https://prove2.me/submissions/12ed7745-8147-46c4-98e2-a2d221d7f10f

import Definitions.Def_LinearChoresCLS_PriceFamily
import Definitions.Def_LinearChoresCLS_RightDeriv

open Finset LinearChoresCLS NetworkEquilibriumCLS.LinearNash

private theorem small_t {n : ℕ} (P : Quadratic n) (ε : ℚ) :
    0 < tParam P ε ∧ tParam P ε ≤ 1/256 := by
  have hL : 8 ≤ chainLength P ε := by
    classical
    unfold chainLength
    split
    next h => exact (Nat.find_spec h).1
    next => exact le_rfl
  refine ⟨by unfold tParam; positivity, ?_⟩
  calc
    _ ≤ (1/2 : ℝ)^8 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hL
    _ = _ := by norm_num

private theorem weights {n : ℕ} (P : Quadratic n) :
    (∀ π : Pair n, 0 < pairWeight P π ∧ pairWeight P π ≤ 2 / (n+1)) ∧
    ∀ j, |lam P * cExt P j| ≤ 1 := by
  classical
  let A := ∑ i, ∑ j, |(P.Q i j : ℝ)|
  let C := ∑ i, |(P.c i : ℝ)|
  have ha : 0 ≤ A := by dsimp [A]; positivity
  have hc : 0 ≤ C := by dsimp [C]; positivity
  have hLam : 0 < lam P := by unfold lam; positivity
  have hn : 0 < (n:ℝ)+1 := by positivity
  have hmass : lam P * (1 + A + C) = 1 / (2*((n:ℝ)+1)) := by
    change 1 / (2 * ((n:ℝ)+1) * (1+A+C)) * _ = _
    field_simp
  have scale {r : ℝ} (hr : |r| ≤ A + C) : |lam P * r| < 1 / ((n:ℝ)+1) := by
    rw [abs_mul, abs_of_pos hLam]
    calc
      _ < lam P * (1 + A + C) := (mul_lt_mul_iff_of_pos_left hLam).mpr (by linarith)
      _ = _ := hmass
      _ < _ := by apply one_div_lt_one_div_of_lt <;> linarith
  have row (i : Fin n) : (∑ j, |(P.Q i j : ℝ)|) ≤ A :=
    Finset.single_le_sum (f := fun k => ∑ j, |(P.Q k j : ℝ)|) (fun k _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) (mem_univ i)
  have term (i j : Fin n) : |(P.Q i j : ℝ)| ≤ A :=
    (Finset.single_le_sum (fun k _ => abs_nonneg (P.Q i k : ℝ)) (mem_univ j)).trans (row i)
  constructor
  · intro π
    have hright : π.1.2 ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) π.2)
    unfold pairWeight wgt
    split <;> rename_i h
    · try rw [dif_neg hright]
      have hrow := (Finset.abs_sum_le_sum_abs (fun k => (P.Q (π.1.2.pred hright) k : ℝ)) univ).trans (row _)
      have hbd := abs_lt.mp (scale (le_trans hrow (by linarith)))
      constructor <;> linarith [show (2:ℝ)/((n:ℝ)+1) = 2*(1/((n:ℝ)+1)) by ring]
    · try rw [dif_neg hright]
      have hbd := abs_lt.mp (scale ((term (π.1.1.pred h) (π.1.2.pred hright)).trans (by linarith)))
      constructor <;> linarith [show (2:ℝ)/((n:ℝ)+1) = 2*(1/((n:ℝ)+1)) by ring]
  · intro j
    have b : |cExt P j| ≤ C := by
      refine Fin.cases ?_ (fun i => ?_) j
      · simpa [cExt,C] using Finset.abs_sum_le_sum_abs (fun i => (P.c i : ℝ)) univ
      · simpa [cExt,C] using (Finset.single_le_sum (fun k _ => abs_nonneg (P.c k : ℝ)) (mem_univ i))
    exact (scale (le_trans b (by linarith))).le.trans (by apply (div_le_iff₀ hn).mpr; simp)

private theorem inc_card {n : ℕ} (j : Fin (n+1)) :
    (incident j).card ≤ n + 1 := by
  classical
  let other (π : Pair n) := if π.1.1 = j then π.1.2 else π.1.1
  classical
  have inj : Set.InjOn other (incident j : Set (Pair n)) := by
    intro a ha b hb he
    have h₁ := (Finset.mem_filter.mp ha).2
    have h₂ := (Finset.mem_filter.mp hb).2
    apply Subtype.ext
    apply Prod.ext <;> dsimp [other] at he <;> split_ifs at he <;>
      grind [a.2,b.2]
  simpa using Finset.card_le_card_of_injOn other
    (t := (univ : Finset (Fin (n+1)))) (fun _ _ => mem_univ _) inj

private theorem market_valid {n : ℕ} (P : Quadratic n) (ε : ℚ) : (completedMarket P ε).Valid := by
  classical
  let t := tParam P ε
  let L := chainLength P ε
  have ht : 0 < t := (small_t P ε).1
  have hs : t ≤ 1/256 := (small_t P ε).2
  have hr : 0 < 1/2 - 4*t := by linarith
  have hs' : 0 < 1 - 4*t := by linarith
  have hq (k : ℕ) : 0 < qPar t k := by unfold qPar; positivity
  have he (π : Pair n) (k : ℕ) : 0 < gadgetEarn P t π k := by
    unfold gadgetEarn
    have := ((weights P).1 π).1
    positivity
  have hsup (π : Pair n) (k : ℕ) : 0 < gadgetSupply P t π k := mul_pos hs' (he π k)
  have hw (j : Fin (n+1)) : (∑ π ∈ incident j, pairWeight P π) ≤ 2 := calc
    _ ≤ ∑ _π ∈ incident j, (2 / ((n:ℝ)+1)) := Finset.sum_le_sum (fun π _ => ((weights P).1 π).2)
    _ = (incident j).card * (2 / ((n:ℝ)+1)) := by simp
    _ ≤ ((n:ℝ)+1) * (2 / ((n:ℝ)+1)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast inc_card j
    _ = 2 := by field_simp
  have hgeom : (∑ k : Fin L, (1/2-4*t)^k.val) ≤ 2 := calc
    _ ≤ ∑ k : Fin L, (1/2:ℝ)^k.val := Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ hr.le (by linarith) k.val)
    _ ≤ 2 := by rw [Fin.sum_univ_eq_sum_range (fun k => (1/2:ℝ)^k) L]; exact sum_geometric_two_le L
  have hinc (j : Fin (n+1)) : (∑ k : Fin L, ∑ π ∈ incident j, gadgetEarn P t π k.val) ≤ 4*t := calc
    _ = (∑ π ∈ incident j, pairWeight P π) * t * ∑ k : Fin L, (1/2-4*t)^k.val := by
      simp only [gadgetEarn, Finset.mul_sum, Finset.sum_mul]
    _ ≤ (2*t)*2 := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right (hw j) ht.le) hgeom
        (Finset.sum_nonneg (fun k _ => pow_nonneg hr.le _)) (by positivity)
    _ = _ := by ring
  have hlin (j : Fin (n+1)) : alpha P t / t * cExt P j ≤ t := calc
    _ = (lam P * cExt P j) * t := by unfold alpha; field_simp
    _ ≤ 1*t := mul_le_mul_of_nonneg_right ((le_abs_self _).trans ((weights P).2 j)) ht.le
    _ = _ := one_mul _
  change (chainMarket P t L).Valid
  refine ⟨?_, ?_, ?_⟩
  · rintro (a | ⟨π,k,r⟩) (j | ⟨ρ,l,b⟩) <;>
      simp only [chainMarket] <;> (try split_ifs) <;> first | exact hq _ | exact one_div_pos.mpr (hq _) | positivity
  · rintro (j | ⟨π,k,r⟩)
    · change 0 < 1 - 3/2*(∑ k : Fin L, ∑ π ∈ incident j, gadgetEarn P t π k.val) - alpha P t / t * cExt P j
      linarith [hinc j, hlin j]
    · exact he _ _
  · rintro (j | ⟨π,k,s⟩)
    · change 0 < 1 - ∑ k : Fin L, ∑ π ∈ incident j, gadgetSupply P t π k.val
      have hle (π : Pair n) (k : ℕ) : gadgetSupply P t π k ≤ gadgetEarn P t π k := by
        unfold gadgetSupply
        nlinarith [mul_pos ht (he π k)]
      have h := Finset.sum_le_sum (s := univ) (fun (k : Fin L) _ =>
        Finset.sum_le_sum (s := incident j) (fun π _ => hle π k.val))
      linarith [hinc j]
    · exact hsup _ _

private theorem input_price_pos {n : ℕ} {x : Fin n → ℝ} (hx : InCube x) {t : ℝ}
    (ht : 0 ≤ t) (j : Fin (n + 1)) : 0 < basicPrice t x j := by
  have he (b : Fin (n + 1)) : 0 ≤ xExt x b := by
    refine Fin.cases ?_ (fun i => ?_) b
    · simp [xExt]
    · simpa [xExt] using (hx i).1
  have hb : 0 ≤ xbar x := by
    unfold xbar
    exact div_nonneg (Finset.sum_nonneg (fun b _ => he b)) (by positivity)
  unfold basicPrice
  have hj := he j
  exact div_pos (by positivity) (by positivity)

private theorem family_pos {n : ℕ} (P : Quadratic n) (ε : ℚ) (x : Fin n → ℝ)
    (hx : InCube x) (i : Chore n (chainLength P ε)) : 0 < completedPrice P ε x i := by
  have ht : 0 < tParam P ε := by unfold tParam; positivity
  have hL : 8 ≤ chainLength P ε := by
    classical
    unfold chainLength
    split
    next h => exact (Nat.find_spec h).1
    next => exact le_rfl
  have hsmall : tParam P ε ≤ (1 / 2 : ℝ) ^ 8 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hL
  have hbase : 0 ≤ 1 / 2 - 4 * tParam P ε := by norm_num at hsmall; linarith
  have hq (k : ℕ) : 0 < qPar (tParam P ε) k := by unfold qPar; positivity
  have layers {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (k : ℕ) :
      0 < (layerOut (tParam P ε) u v k).1 ∧ 0 < (layerOut (tParam P ε) u v k).2 := by
    induction k with
    | zero => exact ⟨div_pos (lt_max_of_lt_left hu) (hq 0), mul_pos (hq 0) (lt_min hu hv)⟩
    | succ k ih => exact ⟨div_pos (lt_max_of_lt_left ih.1) (hq _), mul_pos (hq _) (lt_min ih.1 ih.2)⟩
  rcases i with j | ⟨π, k, s⟩
  · exact input_price_pos hx ht.le j
  · have h := layers (input_price_pos hx ht.le π.1.1) (input_price_pos hx ht.le π.1.2) k.val
    cases s <;> first | exact h.1 | exact h.2


open Finset LinearChoresCLS NetworkEquilibriumCLS.LinearNash Filter Set Topology

private abbrev RD (f : ℝ → ℝ) := DifferentiableWithinAt ℝ f (Ioi 0) 0
private theorem slope_iff (f : ℝ → ℝ) (d : ℝ) :
    HasDerivWithinAt f d (Ioi 0) 0 ↔ HasRightDerivAt0 f d := by
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)]
  have he : slope f 0 = (fun h : ℝ => h⁻¹ • (f h - f 0)) := by funext h; simp [slope_def_module]
  rw [he]; rfl
private theorem maxRD {f g : ℝ → ℝ} (hf : RD f) (hg : RD g) : RD (fun h => max (f h) (g h)) := by
  rcases lt_trichotomy (f 0) (g 0) with hl | he | hl
  · exact hg.congr_of_eventuallyEq ((hf.continuousWithinAt.tendsto.eventually_lt
      hg.continuousWithinAt.tendsto hl).mono (fun _ h => max_eq_right h.le)) (max_eq_right hl.le)
  · let df := derivWithin f (Ioi 0) 0
    let dg := derivWithin g (Ioi 0) 0
    have af := (slope_iff _ _).mp hf.hasDerivWithinAt
    have ag := (slope_iff _ _).mp hg.hasDerivWithinAt
    apply HasDerivWithinAt.differentiableWithinAt (f' := max df dg)
    apply (slope_iff _ _).mpr
    apply (af.max ag).congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 ≤ h⁻¹ := inv_nonneg.mpr (le_of_lt (show 0 < h from hh))
    simp only [smul_eq_mul, he, max_self, ← mul_max_of_nonneg _ _ hh', max_sub_sub_right]
  · exact hf.congr_of_eventuallyEq ((hg.continuousWithinAt.tendsto.eventually_lt
      hf.continuousWithinAt.tendsto hl).mono (fun _ h => max_eq_left h.le)) (max_eq_left hl.le)

private theorem minRD {f g : ℝ → ℝ} (hf : RD f) (hg : RD g) : RD (fun h => min (f h) (g h)) := by
  have he : (fun h => min (f h) (g h)) = -(fun h => max ((-f) h) ((-g) h)) := by
    funext h; simp only [Pi.neg_apply]; rcases le_total (f h) (g h) with a | a
    · rw [min_eq_left a, max_eq_left (neg_le_neg a), neg_neg]
    · rw [min_eq_right a, max_eq_right (neg_le_neg a), neg_neg]
  rw [he]; exact (maxRD hf.neg hg.neg).neg

private theorem priceRD {n : ℕ} (P : Quadratic n) (ε : ℚ) {x : Fin n → ℝ} (hx : InCube x)
    (v : Fin n → ℝ) (j : Chore n (chainLength P ε)) :
    RD (fun h => completedPrice P ε (x + h • v) j) := by
  let t := tParam P ε
  have ht : 0 < t := by dsimp [t,tParam]; positivity
  have ext (b : Fin (n+1)) : RD (fun h => xExt (x + h • v) b) := by
    refine Fin.cases ?_ (fun i => ?_) b
    · simpa [xExt] using (differentiableWithinAt_const (𝕜 := ℝ) (0:ℝ) : RD (fun _ => 0))
    · change RD (fun h => x i + h * v i)
      exact
        (differentiableWithinAt_const (x i)).add (differentiableWithinAt_id.mul (differentiableWithinAt_const (v i)) : RD (fun h => h * v i))
  have avg : RD (fun h => xbar (x+h • v)) :=
    (DifferentiableWithinAt.fun_sum (u := univ) (fun b _ => ext b)).div_const _
  have av0 : 0 ≤ xbar x := by
    unfold xbar
    refine div_nonneg (Finset.sum_nonneg (fun b _ => ?_)) (by positivity)
    exact Fin.cases (by simp [xExt]) (fun i => by simpa [xExt] using (hx i).1) b
  have basic (b : Fin (n+1)) : RD (fun h => basicPrice t (x+h • v) b) := by
    apply ((differentiableWithinAt_const 1).add ((differentiableWithinAt_const t).mul (ext b))).div
      ((differentiableWithinAt_const 1).add ((differentiableWithinAt_const t).mul avg))
    simp only [Pi.add_apply, Pi.mul_apply, zero_smul, add_zero]
    positivity
  have layer {u v' : ℝ → ℝ} (hu : RD u) (hv : RD v') (k : ℕ) :
      RD (fun h => (layerOut t (u h) (v' h) k).1) ∧ RD (fun h => (layerOut t (u h) (v' h) k).2) := by
    induction k with
    | zero => exact ⟨(maxRD hu hv).div_const _, (differentiableWithinAt_const _).mul (minRD hu hv)⟩
    | succ k ih => exact ⟨(maxRD ih.1 ih.2).div_const _, (differentiableWithinAt_const _).mul (minRD ih.1 ih.2)⟩
  rcases j with j | ⟨π,k,s⟩
  · exact basic j
  · cases s <;> first | exact (layer (basic π.1.1) (basic π.1.2) k.val).1 | exact (layer (basic π.1.1) (basic π.1.2) k.val).2


theorem solution {n : ℕ} (hn : 0 < n) (P : Quadratic n) (ε : ℚ) (hε : 0 < ε) :
    ∀ x : Fin n → ℝ, InCube x → ∀ (i : Fin n) (s : Bool), FeasibleCoordDir x i s →
      ∃ D : Chore n (chainLength P ε) → ℝ,
        HasRightDerivAt0 (fun h => completedNormPrice P ε (x + h • coordDir i s)) D := by
  intro x hx i s _
  let v := coordDir i s
  let t := tParam P ε
  let L := chainLength P ε
  have ht : 0 < totalPay P t L x := Finset.sum_pos
    (fun j _ => mul_pos ((market_valid P ε).2.2 j) (family_pos P ε x hx j)) Finset.univ_nonempty
  have hT : RD (fun h => totalPay P t L (x + h • v)) := DifferentiableWithinAt.fun_sum
    (fun j _ => (differentiableWithinAt_const ((completedMarket P ε).supply j)).mul (priceRD P ε hx v j))
  have hj (j : Chore n L) : RD (fun h => completedNormPrice P ε (x + h • v) j) :=
    ((differentiableWithinAt_const _).div hT (by simpa using ht.ne')).mul (priceRD P ε hx v j)
  refine ⟨fun j => derivWithin (fun h : ℝ => completedNormPrice P ε (x + h • v) j) (Ioi 0) 0, ?_⟩
  exact tendsto_pi_nhds.mpr (fun j => (slope_iff _ _).mp (hj j).hasDerivWithinAt)

