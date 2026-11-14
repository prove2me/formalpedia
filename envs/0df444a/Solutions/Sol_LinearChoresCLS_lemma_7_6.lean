-- Prove2me | solution 1 for LinearChoresCLS.lemma_7_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Weiqiang
-- created : 2026-11-13T20:48:28.858148+00:00
-- url     : https://prove2.me/submissions/a9bf97ea-00ca-46ca-a7b1-8a2672374df4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_LinearChoresCLS_unnormalized_objective_expansion
import Theorems.Thm_LinearChoresCLS_theorem_5_1
import Theorems.Thm_LinearChoresCLS_theorem_6_9
import Theorems.Thm_LinearChoresCLS_theorem_6_10
import Theorems.Thm_LinearChoresCLS_theorem_6_12

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

open Finset LinearChoresCLS NetworkEquilibriumCLS.LinearNash

private theorem scale_layers (t u v c : ℝ) (hc : 0 < c) (k : ℕ) :
    layerOut t (c*u) (c*v) k = (c*(layerOut t u v k).1,c*(layerOut t u v k).2) := by
  induction k with
  | zero => simp only [layerOut, ← mul_max_of_nonneg _ _ hc.le, ← mul_min_of_nonneg _ _ hc.le]; congr 1 <;> ring
  | succ k ih =>
    simp only [layerOut,ih, ← mul_max_of_nonneg _ _ hc.le, ← mul_min_of_nonneg _ _ hc.le]
    congr 1 <;> ring

private theorem nonincident {n : ℕ} (P : Quadratic n) (t : ℝ) (ht : 0 ≤ t) (L : ℕ)
    (x : Fin n → ℝ) (i : Fin n) (h : ℝ) (hx : InCube x)
    (hy : InCube (x + h • Pi.single i (1 : ℝ))) (π : Pair n) (hp : π ∉ incident i.succ) :
    chainRem P t L π (x+h • Pi.single i (1:ℝ)) = chainRem P t L π x := by
  classical
  let y := x+h • Pi.single i (1:ℝ)
  have he (j : Fin (n+1)) (hj : j ≠ i.succ) : xExt y j = xExt x j := by
    revert hj
    refine Fin.cases (by simp [xExt]) (fun a => ?_) j
    intro ha
    have hne : a ≠ i := by intro e; exact ha (congrArg Fin.succ e)
    simp [y,xExt,Pi.single_apply,hne,Ne.symm hne]
  have hj := (show π.1.1 ≠ i.succ ∧ π.1.2 ≠ i.succ by simpa [incident] using hp)
  have pos (v : Fin n → ℝ) (hv : InCube v) : 0 < 1+t*xbar v := by
    have hbar : 0 ≤ xbar v := by
      unfold xbar; apply div_nonneg _ (by positivity)
      exact sum_nonneg (fun j _ => Fin.cases (by simp [xExt]) (fun a => by simpa [xExt] using (hv a).1) j)
    positivity
  let c := (1+t*xbar x)/(1+t*xbar y)
  have hc : 0<c := div_pos (pos x hx) (pos y hy)
  have ratio (j : Fin (n+1)) (hj : j ≠ i.succ) : basicPrice t y j = c*basicPrice t x j := by
    unfold basicPrice; rw [he j hj]; dsimp only [c]; field_simp [(pos x hx).ne',(pos y hy).ne']
  have hd (k : ℕ) : chainDelta t π y k = chainDelta t π x k := by
    cases k with
    | zero => simp only [chainDelta,ratio _ hj.1,ratio _ hj.2,mul_div_mul_left _ _ hc.ne']
    | succ k => simp only [chainDelta,ratio _ hj.1,ratio _ hj.2,scale_layers t _ _ c hc,mul_div_mul_left _ _ hc.ne']
  change chainRem P t L π y = _
  simp only [chainRem,hd,he _ hj.1,he _ hj.2]

private theorem incident_mass {n : ℕ} (P : Quadratic n) (i : Fin n) :
    (∑ π ∈ incident i.succ, pairWeight P π) ≤ 1 := by
  classical
  let u := 1/((n:ℝ)+1)
  let A (k : Fin n) := (P.Q i k : ℝ)
  let f : Fin (n+1) → ℝ := Fin.cons (u - lam P*∑ k, A k) (fun k => u+lam P*A k)
  let other (π : Pair n) := if π.1.1 = i.succ then π.1.2 else π.1.1
  have bij : (∑ π ∈ incident i.succ, pairWeight P π) = ∑ j ∈ univ.erase i.succ, f j := by
    apply sum_bij (fun π _ => other π)
    · intro π h
      have := (mem_filter.mp h).2
      have := π.2
      simp only [mem_erase,mem_univ,and_true,other]
      split_ifs <;> grind
    · intro a ha b hb he
      have h₁ := (mem_filter.mp ha).2
      have h₂ := (mem_filter.mp hb).2
      apply Subtype.ext
      apply Prod.ext <;> dsimp [other] at he <;> split_ifs at he <;> grind [a.2,b.2]
    · intro j hj
      have hne := (mem_erase.mp hj).1
      rcases lt_or_gt_of_ne hne with h | h
      · refine ⟨⟨(j,i.succ),h⟩, by simp [incident], by simp [other,hne]⟩
      · refine ⟨⟨(i.succ,j),h⟩, by simp [incident], by simp [other]⟩
    · rintro ⟨⟨a,b⟩,hab⟩ h
      have hh : a=i.succ ∨ b=i.succ := (mem_filter.mp h).2
      rcases hh with rfl | rfl
      · have hb : b ≠ 0 := ne_of_gt ((Fin.zero_le _).trans_lt hab)
        have fb : f b = u + lam P*A (b.pred hb) := by
          conv_lhs => rw [← Fin.succ_pred b hb]
          rfl
        simp [other,pairWeight,wgt,hb,fb,A,u]
      · have hn : a ≠ i.succ := ne_of_lt hab
        dsimp only [other]; rw [if_neg hn]
        by_cases hz : a = 0
        · subst a; simp [f,A,u,pairWeight,wgt]
        · have fa : f a = u + lam P*A (a.pred hz) := by
            conv_lhs => rw [← Fin.succ_pred a hz]
            rfl
          simp [fa,A,u,pairWeight,wgt,hz,P.symmetric (a.pred hz) i]
  rw [bij,sum_erase_eq_sub (mem_univ _),Fin.sum_univ_succ]
  simp only [f,Fin.cons_zero,Fin.cons_succ,Finset.sum_add_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hbase : (n:ℝ)*u = 1-u := by dsimp [u]; field_simp; ring
  have hdiag : |lam P*A i| ≤ u := by
    let T := ∑ j, ∑ k, |(P.Q j k : ℝ)|
    let C := ∑ j, |(P.c j : ℝ)|
    have hT : 0 ≤ T := by dsimp [T]; positivity
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have row : ∑ k, |(P.Q i k : ℝ)| ≤ T := single_le_sum
      (fun j _ => sum_nonneg (fun k _ => abs_nonneg (P.Q j k : ℝ))) (mem_univ i)
    have entry : |A i| ≤ T := (single_le_sum (fun k _ => abs_nonneg (P.Q i k : ℝ)) (mem_univ i)).trans row
    have hl : 0 < lam P := by unfold lam; positivity
    rw [abs_mul,abs_of_pos hl]; dsimp only [u]
    calc
      _ ≤ lam P * (1+T+C) := mul_le_mul_of_nonneg_left (by linarith) hl.le
      _ = 1 / (2*((n:ℝ)+1)) := by dsimp [lam,T,C]; field_simp
      _ ≤ _ := by apply one_div_le_one_div_of_le <;> linarith
  linarith [(abs_le.mp hdiag).1]
private theorem tolerance {n : ℕ} (P : Quadratic n) (ε : ℚ) (hε : 0<ε) :
    8 ≤ chainLength P ε ∧ tParam P ε ≤ lam P * (ε:ℝ)/64 := by
  classical
  have hl : 0 < lam P := by unfold lam; positivity
  have hr : 0 < (ε:ℝ) := by exact_mod_cast hε
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one (show 0 < lam P*(ε:ℝ)/64 by positivity) (show (1/2:ℝ) < 1 by norm_num)
  have ex : ∃ m : ℕ, 8 ≤ m ∧ (1/2:ℝ)^m ≤ lam P*(ε:ℝ)/64 :=
    ⟨max 8 k,le_max_left _ _,(pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right 8 k)).trans hk.le⟩
  simpa only [tParam,chainLength,dif_pos ex] using Nat.find_spec ex

theorem solution {n : ℕ} (hn : 0 < n) (P : Quadratic n) (ε : ℚ) (hε : 0 < ε) :
    ∃ (C : ℝ) (R : (Fin n → ℝ) → ℝ),
      (∀ x, InCube x → (completedMarket P ε).Psi (completedNormPrice P ε x) =
        C + alpha P (tParam P ε) * quadraticValue P x + R x) ∧
      0 ≤ 20 * tParam P ε ^ 3 ∧ 20 * tParam P ε ^ 3 ≤ alpha P (tParam P ε) * ε ∧
      ∀ (x : Fin n → ℝ) (i : Fin n) (h : ℝ), InCube x → InCube (x + h • Pi.single i (1 : ℝ)) →
        |R (x + h • Pi.single i (1 : ℝ)) - R x| ≤ 20 * tParam P ε ^ 3 * |h| := by
  classical
  let t := tParam P ε
  let L := chainLength P ε
  have ht : 0<t := (small_t P ε).1
  have ht1 : t ≤ 1 := by linarith [(small_t P ε).2]
  have ht8 : t < 1/8 := by linarith [(small_t P ε).2]
  obtain ⟨hL,hsize⟩ := tolerance P ε hε
  obtain ⟨C,hC⟩ := unnormalized_objective_expansion hn P ε hε
  obtain ⟨hnorm,hN,_⟩ := theorem_6_12 hn P t L (by dsimp [L]; omega) ht ht8
  let R := fun x => R0 t x - (∑ π : Pair n, chainRem P t L π x) + Rlin P t x + Rnorm P t L x
  refine ⟨C,R,?_,by positivity,?_,?_⟩
  · intro x hx
    exact (hnorm x hx).trans (by rw [show (chainMarket P t L).Psi (priceFam t L x) = _ from hC x hx]; dsimp only [R]; ring)
  · change 20*t^3 ≤ lam P*t^2*(ε:ℝ)
    have h : 20*t ≤ lam P*(ε:ℝ) := by dsimp only [t]; linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (sq_nonneg t)]
  · intro x i h hx hy
    let y := x+h • Pi.single i (1:ℝ)
    let E := fun π => chainRem P t L π y - chainRem P t L π x
    have heq : (∑ π : Pair n, E π) = ∑ π ∈ incident i.succ, E π := by
      symm; apply sum_subset (subset_univ _); intro π _ hp
      exact sub_eq_zero.mpr (nonincident P t ht.le L x i h hx hy π hp)
    have hchain : |∑ π : Pair n, E π| ≤ 12*t^3*|h| := calc
      _ = _ := congrArg abs heq
      _ ≤ ∑ π ∈ incident i.succ, |E π| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ π ∈ incident i.succ, pairWeight P π * (12*t^3*|h|) := by
        apply sum_le_sum; intro π _
        exact ((theorem_6_9 hn P ε hε π).2.1 x i h hx hy).trans_eq (by dsimp only [t]; ring)
      _ = (∑ π ∈ incident i.succ, pairWeight P π) * (12*t^3*|h|) := (sum_mul ..).symm
      _ ≤ 1*(12*t^3*|h|) := mul_le_mul_of_nonneg_right (incident_mass P i) (by positivity)
      _ = _ := one_mul _
    have h0 := (theorem_5_1 t ht ht1).2.1 x i h hx hy
    have hlin := (theorem_6_10 P t ht ht1).2.1 x i h hx hy
    have hnorm' := hN x i h hx hy
    have hc : t^3/(2*((n:ℝ)+1)) ≤ t^3 := by apply (div_le_iff₀ (by positivity)).mpr; nlinarith [mul_nonneg (show 0 ≤ (n:ℝ) by positivity) (pow_nonneg ht.le 3),pow_nonneg ht.le 3]
    have hlin' := hlin.trans (mul_le_mul_of_nonneg_right hc (abs_nonneg h))
    change |R y-R x| ≤ _
    dsimp only [E] at hchain
    rw [Finset.sum_sub_distrib] at hchain
    change |R0 t y - R0 t x| ≤ _ at h0
    change |Rlin P t y - Rlin P t x| ≤ _ at hlin'
    change |Rnorm P t L y - Rnorm P t L x| ≤ _ at hnorm'
    dsimp only [R]; apply abs_le.mpr
    have H₀ := abs_le.mp h0
    have H₁ := abs_le.mp hlin'
    have H₂ := abs_le.mp hnorm'
    have H₃ := abs_le.mp hchain
    change -(20*t^3*|h|) ≤ _ ∧ _ ≤ 20*t^3*|h|
    constructor <;> nlinarith [mul_nonneg (pow_nonneg ht.le 3) (abs_nonneg h)]
