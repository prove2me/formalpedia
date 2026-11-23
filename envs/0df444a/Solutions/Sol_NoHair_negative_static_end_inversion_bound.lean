-- Prove2me | solution 1 for NoHair.negative_static_end_inversion_bound
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:57:41.111613+00:00
-- url     : https://prove2.me/submissions/95afa1d1-be9e-4934-9550-c241379d952d

import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

private abbrev X := ADMPoint

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    HasStaticMinusInversionBound N h := by
  classical
  obtain ⟨R₀,C,rp,cp,fall⟩ := c.falloff 0
  let R := max R₀ (20*C)
  have rp' : 0 < R := rp.trans_le (le_max_left _ _)
  let g := staticPositiveMetric (fun y => -N y) h
  let J := EuclideanGeometry.inversion (0:X) 1
  have bound (x : X) (hx : R < ‖x‖) (v : X) :
      ‖x‖^4 * staticChartQuadratic g x v ≤ (2*C ^ 4) * ‖v‖^2 := by
    have r := rp'.trans hx
    have scale : C / ‖x‖ ≤ 1/20 := (div_le_iff₀ r).mpr (by linarith only [(max_lt_iff.mp hx).2])
    have af := fall x (max_lt_iff.mp hx).1
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,Nat.zero_add,pow_one] at af
    let w := (1 + -N x)/2
    have aw : |w| = |N x-1|/2 := by
      dsimp only [w]
      rw [abs_div,show 1 + -N x = -(N x-1) by ring,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have small : |‖x‖*w| ≤ C := by
      rw [abs_mul,abs_of_pos r,aw]
      have h := (le_div_iff₀ r).mp af.1
      nlinarith only [h,cp]
    have factor : ‖x‖^4*w^4 ≤ C ^ 4 := calc
      _ = |‖x‖*w|^4 := by rw [←mul_pow,←abs_pow,abs_of_nonneg (by positivity : 0 ≤ (‖x‖*w)^4)]
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) small 4
    let δ := (1 : Matrix (Fin 3) (Fin 3) ℝ)
    have vi (i : Fin 3) : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i
    have comp (i j : Fin 3) : |(h x i j-δ i j)*v i*v j| ≤ (1/20:ℝ)*‖v‖^2 := by
      rw [abs_mul,abs_mul]
      calc _ ≤ ((1/20:ℝ)*‖v‖)*‖v‖ := mul_le_mul
             (mul_le_mul ((af.2 i j).trans scale) (vi i) (abs_nonneg _) (by norm_num))
             (vi j) (abs_nonneg _) (by positivity)
           _ = _ := by ring
    have flat : (∑ i : Fin 3, ∑ j : Fin 3, δ i j*v i*v j) = ‖v‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp +decide [Fin.sum_univ_three,δ,Matrix.one_apply] <;> ring
    let H := ∑ i : Fin 3, ∑ j : Fin 3, h x i j*v i*v j
    have dev : |H-‖v‖^2| ≤ 9/20*‖v‖^2 := calc
      _ = |∑ i : Fin 3, ∑ j : Fin 3, (h x i j-δ i j)*v i*v j| := by
        rw [← flat]; dsimp only [H];simp only [sub_mul,Finset.sum_sub_distrib]
      _ ≤ ∑ i : Fin 3, |∑ j : Fin 3, (h x i j-δ i j)*v i*v j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, (1/20:ℝ)*‖v‖^2 := Finset.sum_le_sum fun i _ =>
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => comp i j)
      _ = _ := by simp [Fin.sum_univ_three]; ring
    have upper : H ≤ 2*‖v‖^2 := by linarith only [(abs_le.mp dev).2,sq_nonneg ‖v‖]
    have sep : staticChartQuadratic g x v = w^4*H := by
      dsimp only [g,staticChartQuadratic,staticPositiveMetric,w,H]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [sep,←mul_assoc]
    calc _ ≤ (‖x‖^4*w^4)*(2*‖v‖^2) := mul_le_mul_of_nonneg_left upper (by positivity)
         _ ≤ C ^ 4*(2*‖v‖^2) := mul_le_mul_of_nonneg_right factor (by positivity)
         _ = _ := by ring
  refine ⟨R,2*C ^ 4,rp',by positivity,bound,?_⟩
  intro y hy hs v
  have yn := (norm_pos_iff.mp hy)
  have radius : ‖J y‖ = 1/‖y‖ := by
    simpa only [J,one_pow,dist_zero_right] using EuclideanGeometry.dist_inversion_center (0:X) y 1
  have far : R < ‖J y‖ := by
    rw [radius,lt_div_iff₀ hy]
    linarith only [(lt_div_iff₀ rp').mp hs]
  have speed : ‖fderiv ℝ J y v‖ = (1/‖y‖)^2 * ‖v‖ := by
    rw [show fderiv ℝ J y = _ from (EuclideanGeometry.hasFDerivAt_inversion (R:=(1:ℝ)) yn).fderiv]
    simp [dist_zero_right,ContinuousLinearMap.smul_apply,norm_smul,abs_of_nonneg (sq_nonneg (1/‖y‖))]
  have hq := bound (J y) far (fderiv ℝ J y v)
  rw [radius,speed] at hq
  apply (mul_le_mul_iff_right₀ (pow_pos (div_pos zero_lt_one hy) 4)).mp
  exact hq.trans_eq (by ring)
