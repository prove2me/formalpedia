-- Prove2me | solution 1 for NoHair.exterior_metric_falloff_gives_weighted_sobolev_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:50:14.513676+00:00
-- url     : https://prove2.me/submissions/b1e2df86-e437-426c-ac34-78fd203d79ff

import Definitions.Def_NoHair_staticReflectionAndCap
import Definitions.Def_NoHair_staticInvertedEndMetric
open NoHair Set Filter MeasureTheory
open scoped Topology ContDiff
private abbrev X := ADMPoint
private abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ
private lemma pointwise_weight (k : ℕ) {r D C : ℝ} (hr : 1 < r) (hd : 0 ≤ D) (hc : 0 < C)
    (bd : D ≤ C/r^(k+1)) :
    ((1+r^2)^k/(1+r^2))*D^2 ≤ (16*((2:ℝ)^k*C^2))*(1+r)^(-4:ℝ) := by
  have rp : 0 < r := zero_lt_one.trans hr
  have p2 : 1+r^2 ≤ 2*r^2 := by nlinarith only [sq_nonneg (r-1),hr]
  have den : 0 < 1+r^2 := by positivity
  have dw : (1+r^2)^k/(1+r^2) ≤ (2*r^2)^k/(r^2) :=
    div_le_div₀ (by positivity) (pow_le_pow_left₀ den.le p2 _) (sq_pos_of_pos rp) (by linarith)
  have pw : (r^2)^k=(r^k)^2 := by rw [←pow_mul,Nat.mul_comm,pow_mul]
  let K:=(2:ℝ)^k*C^2
  have kpos : 0 ≤ K := by dsimp [K]; positivity
  calc
    _ ≤ ((2*r^2)^k/r^2)*(C/r^(k+1))^2 :=
      mul_le_mul dw (pow_le_pow_left₀ hd bd 2) (sq_nonneg _) (by positivity)
    _ = K/r^4 := by rw [mul_pow,pw,pow_succ]; dsimp only [K]; field_simp [rp.ne'] <;> ring
    _ ≤ _ := by
      rw [Real.rpow_neg (by positivity : 0≤1+r) (4:ℝ),show (1+r)^(4:ℝ)=(1+r)^4 by norm_cast,←div_eq_mul_inv]
      apply (div_le_div_iff₀ (pow_pos rp 4) (by positivity)).2
      have q:=pow_le_pow_left₀ (by positivity : 0≤1+r) (by linarith : 1+r≤2*r) 4
      change K*(1+r)^4 ≤ (16*K)*r^4
      nlinarith only [mul_nonneg kpos (sub_nonneg.mpr q)]

theorem solution (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) (B : ℝ) (s : ℕ)
    (smooth : ∀ x : ADMPoint, B < ‖x‖ → ∀ i j, ContDiffAt ℝ ∞ (fun z => h z i j) x)
    (falloff : ∀ k : ℕ, ∃ L C : ℝ, 0 < L ∧ 0 < C ∧ ∀ x : ADMPoint, L < ‖x‖ → ∀ i j,
       ‖iteratedFDeriv ℝ k (fun z => h z i j-(1:Matrix (Fin 3) (Fin 3) ℝ) i j) x‖ ≤ C/‖x‖^(k+1)) :
    ∃ R : ℝ, max B 1 ≤ R ∧ ∀ k : ℕ, k ≤ s → ∀ i j : Fin 3, IntegrableOn
      (fun x : ADMPoint => ((1+‖x‖^2)^k/(1+‖x‖^2))*
        ‖iteratedFDeriv ℝ k (fun z => h z i j-(1:Matrix (Fin 3) (Fin 3) ℝ) i j) x‖^2)
      {x : ADMPoint | R < ‖x‖} := by
  choose L C lp cp bounds using falloff
  let t:=∑ k ∈ Finset.range (s+1), |L k|
  have tp : 0 ≤ t := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let R:=max B 1+t
  have hm : max B 1 ≤ R := le_add_of_nonneg_right tp
  have ht {k : ℕ} (hk : k ≤ s) : L k ≤ R := by
    have hsum : |L k| ≤ t := Finset.single_le_sum (f:=fun j : ℕ => |L j|) (fun j _ => abs_nonneg (L j)) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    have one := le_max_right B (1:ℝ)
    dsimp only [R]
    linarith only [le_abs_self (L k),hsum,one]
  refine ⟨R,hm,?_⟩
  intro k hk i j
  let U:={x : X | R < ‖x‖}
  let F:=fun z : X => h z i j-(1:Mat) i j
  let g:=fun x:X => ((1+‖x‖^2)^k/(1+‖x‖^2))*‖iteratedFDeriv ℝ k F x‖^2
  have uopen : IsOpen U := isOpen_lt continuous_const continuous_norm
  have cg : ContinuousOn g U := by
    intro x hx
    have bfar : B < ‖x‖ := ((le_max_left B 1).trans hm).trans_lt hx
    have sc : ContDiffAt ℝ ∞ F x := (smooth x bfar i j).sub contDiffAt_const
    have cd := (sc.continuousAt_iteratedFDeriv (k:=k) (WithTop.coe_le_coe.mpr le_top)).norm
    have cn : ContinuousAt (fun z : X => 1+‖z‖^2) x := by fun_prop
    exact (((cn.pow k).div cn (by positivity)).mul (cd.pow 2)).continuousWithinAt
  have hint := integrable_one_add_norm (E:=X) (μ:=volume) (r:=(4:ℝ))
    (by norm_num [finrank_euclideanSpace] : (Module.finrank ℝ X : ℝ)<4)
  change IntegrableOn g U
  apply ((hint.const_mul (16*((2:ℝ)^k*(C k)^2))).integrableOn).mono' (cg.aestronglyMeasurable uopen.measurableSet)
  filter_upwards [ae_restrict_mem (μ:=volume) uopen.measurableSet] with x hx
  have rfar : 1 < ‖x‖ := ((le_max_right B 1).trans hm).trans_lt hx
  change |((1+‖x‖^2)^k/(1+‖x‖^2))*‖iteratedFDeriv ℝ k F x‖^2| ≤ _
  rw [abs_of_nonneg (by positivity)]
  exact pointwise_weight k rfar (norm_nonneg _) (cp k) (bounds k x ((ht hk).trans_lt hx) i j)
