-- Prove2me | solution 1 for ModernOnlineLearning.LowerBounds.phi_properties
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T08:26:07.029998+00:00
-- url     : https://prove2.me/submissions/bc36bc0a-624f-42f0-953b-cdbb219b58c4

import Mathlib
import Definitions.Def_ModernOnlineLearning_LowerBounds_phi
set_option autoImplicit false
open Filter Set
open scoped Topology
open ModernOnlineLearning.LowerBounds

private lemma phi_pos (α : ℝ) (ha : 0 < α) (hb : α < 1) : 0 < phi α := by
  let q := 1-α
  have hq : 0 < q := by dsimp [q];linarith
  have hq1 : q < 1 := by dsimp [q];linarith
  have hpow : (2 : ℝ)^q < 1+q := by
    simpa only [one_add_one_eq_two,mul_one] using rpow_one_add_lt_one_add_mul_self (s := (1 : ℝ))
      (by norm_num) one_ne_zero hq hq1
  have hpowpos : 0 < (2 : ℝ)^q := Real.rpow_pos_of_pos (by norm_num) _
  have hh : (1/2 : ℝ)^q = 1/(2 : ℝ)^q := by rw [Real.div_rpow (by norm_num) (by norm_num),Real.one_rpow]
  have he : phi α = ((1+q)-(2 : ℝ)^q)/((1+q)*q*(2 : ℝ)^q) := by
    have hd : 2-α = 1+q := by dsimp [q];ring
    unfold phi
    rw [hd,show 1-α=q from rfl,hh]
    field_simp
    ring
  rw [he]
  exact div_pos (sub_pos.mpr hpow) (by positivity)

private lemma phi_limit : Tendsto phi (𝓝[<] (1 : ℝ)) (𝓝 (1-Real.log 2)) := by
  have hd := (Real.hasStrictDerivAt_const_rpow (a := (1/2 : ℝ)) (by norm_num) 0).hasDerivAt
  have hquot : Tendsto (fun q : ℝ => ((1/2 : ℝ)^q-1)/q)
      (𝓝[>] 0) (𝓝 (-Real.log 2)) := by
    simpa [Real.log_div,Real.log_one,div_eq_inv_mul] using hd.tendsto_slope_zero_right
  have hsub : Tendsto (fun a : ℝ => 1-a) (𝓝[<] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun a : ℝ => 1-a) 1 := by fun_prop
      convert hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ))) using 1 <;> norm_num
    · filter_upwards [self_mem_nhdsWithin] with a ha
      change a < 1 at ha
      exact sub_pos.mpr ha
  have hfirst : Tendsto (fun a : ℝ => 1/(2-a)) (𝓝[<] 1) (𝓝 1) := by
    have hh : ContinuousAt (fun a : ℝ => 1/(2-a)) 1 := by fun_prop (disch := norm_num)
    convert hh.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ))) using 1 <;> norm_num
  change Tendsto (fun a => phi a) _ _
  simpa [phi,Function.comp_def,sub_eq_add_neg] using hfirst.add (hquot.comp hsub)


private lemma exp_neg_le_quadratic (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1-x+x^2/2 := by
  let F := fun t : ℝ => 1-t+t^2/2-Real.exp (-t)
  have hd : ∀ t, HasDerivAt F (-1+t+Real.exp (-t)) t := by
    intro t
    convert (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).add
      (((hasDerivAt_id t).pow 2).div_const 2)).sub ((hasDerivAt_id t).neg.exp) using 1
    all_goals first | rfl | (simp only [id_eq,Pi.neg_apply]; ring)
  have hm : Monotone F := monotone_of_deriv_nonneg (fun t => (hd t).differentiableAt)
    (fun t => by rw [(hd t).deriv];linarith [Real.add_one_le_exp (-t)])
  have hh := hm hx
  dsimp [F] at hh
  simp only [neg_zero,Real.exp_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_div,sub_zero,add_zero,sub_self] at hh
  linarith

private lemma phi_lt_limit (α : ℝ) (ha : 0 < α) (hb : α < 1) : phi α < 1-Real.log 2 := by
  let q := 1-α
  have hq : 0 < q := by dsimp [q];linarith
  have hq1 : q < 1 := by dsimp [q];linarith
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2 : (Real.log 2)^2 < 1 := by nlinarith [Real.log_two_lt_d9]
  have ht := exp_neg_le_quadratic (q*Real.log 2) (mul_nonneg hq.le hlog)
  have hepow : (1/2 : ℝ)^q = Real.exp (-(q*Real.log 2)) := by
    rw [Real.rpow_def_of_pos (by norm_num),Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),Real.log_one]
    congr 1;ring
  have hd : 0 < 1+q := by positivity
  have hfactor : (Real.log 2)^2/2 < 1/(1+q) := by
    calc
      (Real.log 2)^2/2 < (1/2 : ℝ) := by linarith
      _ < 1/(1+q) := by apply (lt_div_iff₀ hd).mpr;linarith
  have hprod := mul_lt_mul_of_pos_right hfactor hq
  have hquot : ((1/2 : ℝ)^q-1)/q ≤ -Real.log 2+q*(Real.log 2)^2/2 := by
    apply (div_le_iff₀ hq).mpr
    rw [hepow]
    nlinarith [ht]
  have he : phi α = 1/(1+q)+((1/2 : ℝ)^q-1)/q := by
    unfold phi
    rw [show 2-α=1+q by dsimp [q];ring]
  rw [he]
  have hid : 1/(1+q)+q/(1+q)=1 := by field_simp
  simp only [div_eq_mul_inv] at hquot hprod hid ⊢
  nlinarith only [hquot,hprod,hid]

theorem solution :
    (∀ α : ℝ, 0 < α → α < 1 → phi α ∈ Set.Ioo 0 (1-Real.log 2)) ∧
    Tendsto phi (𝓝[<] (1 : ℝ)) (𝓝 (1-Real.log 2)) ∧
    (3/10 : ℝ) ≤ 1-Real.log 2 := by
  refine ⟨fun α ha hb => ⟨phi_pos α ha hb,phi_lt_limit α ha hb⟩,phi_limit,?_⟩
  linarith [Real.log_two_lt_d9]

