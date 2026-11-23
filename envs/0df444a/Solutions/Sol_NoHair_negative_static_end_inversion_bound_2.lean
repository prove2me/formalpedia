-- Prove2me | solution 2 for NoHair.negative_static_end_inversion_bound
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:01:34.610706+00:00
-- url     : https://prove2.me/submissions/bed47572-c17a-4351-a207-e2e4cd88004c

import Definitions.Def_NoHair_staticReflectionAndCap

noncomputable section

open NoHair Set Filter
open scoped ContDiff Topology

private abbrev X := ADMPoint
private abbrev K := Fin 3
private abbrev Mat := Matrix K K ℝ

private lemma bound_form (h : X → Mat) (x v : X) (A : ℝ) (hA : 0 ≤ A)
    (hg : ∀ i j : K, |h x i j| ≤ A) :
    staticChartQuadratic h x v ≤ 9*A*‖v‖^2 := by
  have coord (i : K) : |v i| ≤ ‖v‖ := PiLp.norm_apply_le v i
  calc
    _ ≤ ∑ _i : K, ∑ _j : K,A*‖v‖*‖v‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply (le_abs_self _).trans
      rw [abs_mul,abs_mul]
      exact mul_le_mul (mul_le_mul (hg i j) (coord i) (abs_nonneg _) hA) (coord j)
        (abs_nonneg _) (mul_nonneg hA (norm_nonneg _))
    _ = _ := by simp only [Fin.sum_univ_three]; ring

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    HasStaticMinusInversionBound N h := by
  let g := staticPositiveMetric (fun y => -N y) h
  let I := EuclideanGeometry.inversion (0:X) 1
  obtain ⟨R,C,hR,hC,hd⟩ := c.falloff 0
  let L := max 1 R
  let A := 9*(C+1)*C^4
  have hL : 0<L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have ha : 0<A := by dsimp [A]; positivity
  have far (x : X) (hx : L<‖x‖) (v : X) : ‖x‖^4*staticChartQuadratic g x v ≤ A*‖v‖^2 := by
    have hx1 : 1 ≤ ‖x‖ := (le_max_left _ _).trans hx.le
    have hr : 0<‖x‖ := zero_lt_one.trans_le hx1
    have d := hd x ((le_max_right _ _).trans_lt hx)
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,Nat.zero_add,pow_one] at d
    have bound (i j : K) : |h x i j| ≤ C+1 := by
      have hid : |(1:Mat) i j| ≤ 1 := by by_cases e : i=j <;> simp [Matrix.one_apply,e]
      calc
        _ = |(h x i j-(1:Mat) i j)+(1:Mat) i j| := by rw [sub_add_cancel]
        _ ≤ _ := abs_add_le _ _
        _ ≤ C+1 := add_le_add ((d.2 i j).trans (div_le_self hC.le hx1)) hid
    let s := (1-N x)/2
    have hq : |‖x‖*s| ≤ C := by
      have hw := (le_div_iff₀ hr).mp d.1
      rw [abs_mul,abs_of_nonneg (norm_nonneg _)]
      dsimp only [s]
      rw [abs_div,abs_sub_comm,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith only [hw,hC]
    have hpow : (‖x‖*s)^4 ≤ C^4 := by
      rw [← (show Even (4:ℕ) from ⟨2,rfl⟩).pow_abs (‖x‖*s)]
      exact pow_le_pow_left₀ (abs_nonneg _) hq 4
    have hg : staticChartQuadratic g x v=s^4*staticChartQuadratic h x v := by
      dsimp only [g,staticChartQuadratic,staticPositiveMetric,s]
      simp only [Fin.sum_univ_three]
      ring
    rw [hg]
    calc
      _ = (‖x‖*s)^4*staticChartQuadratic h x v := by ring
      _ ≤ (‖x‖*s)^4*(9*(C+1)*‖v‖^2) :=
        mul_le_mul_of_nonneg_left (bound_form h x v (C+1) (by positivity) bound) (by positivity)
      _ ≤ C^4*(9*(C+1)*‖v‖^2) := mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = A*‖v‖^2 := by dsimp [A]; ring
  refine ⟨L,A,hL,ha,far,?_⟩
  intro y hy hsmall v
  have hy0 := norm_pos_iff.mp hy
  have nr : ‖I y‖=1/‖y‖ := by
    simpa only [dist_zero_right,one_pow] using EuclideanGeometry.dist_inversion_center (0:X) y 1
  have big : L<‖I y‖ := by
    rw [nr,lt_div_iff₀ hy]
    have t := (lt_div_iff₀ hL).mp hsmall
    linarith only [t]
  have nd : ‖fderiv ℝ I y v‖=(1/‖y‖)^2*‖v‖ := by
    change ‖fderiv ℝ (EuclideanGeometry.inversion (0:X) 1) y v‖=_
    rw [(EuclideanGeometry.hasFDerivAt_inversion (R:=1) hy0).fderiv,ContinuousLinearMap.smul_apply,norm_smul]
    simp [dist_zero_right,abs_of_pos hy]
  have e:=far (I y) big (fderiv ℝ I y v)
  rw [nr,nd] at e
  change staticChartQuadratic g (I y) (fderiv ℝ I y v) ≤ _
  apply (mul_le_mul_iff_right₀ (pow_pos (one_div_pos.mpr hy) 4)).mp
  calc
    _ ≤ _ := e
    _ = _ := by ring
