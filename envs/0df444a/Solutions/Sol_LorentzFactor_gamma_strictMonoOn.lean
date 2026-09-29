-- Prove2me | solution 1 for LorentzFactor.gamma_strictMonoOn
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:24:06.365163+00:00
-- url     : https://prove2.me/submissions/f5c9d62c-dfec-4cc5-9e54-5de2298d327f

import Mathlib
import Definitions.Def_LorentzFactorDefs

open Filter Topology
open LorentzFactor

theorem W2p_LorentzFactor_pos (β : ℝ) (h : |β| < 1) : 0 < 1 - β ^ 2 := by
  have := abs_lt.mp h
  nlinarith

theorem W2p_LorentzFactor_gamma_sq (β : ℝ) (h : |β| < 1) :
    gamma β ^ 2 * (1 - β ^ 2) = 1 := by
  have ha := W2p_LorentzFactor_pos β h
  unfold gamma
  rw [div_pow, one_pow, Real.sq_sqrt ha.le, one_div_mul_cancel ha.ne']

theorem W2p_LorentzFactor_gamma_pos (β : ℝ) (h : |β| < 1) : 0 < gamma β := by
  have ha := W2p_LorentzFactor_pos β h
  unfold gamma
  exact one_div_pos.mpr (Real.sqrt_pos.mpr ha)

theorem W2p_LorentzFactor_velAdd_abs (β₁ β₂ : ℝ) (h₁ : |β₁| < 1) (h₂ : |β₂| < 1) :
    |velAdd β₁ β₂| < 1 := by
  obtain ⟨a1, a2⟩ := abs_lt.mp h₁
  obtain ⟨b1, b2⟩ := abs_lt.mp h₂
  have hD : 0 < 1 + β₁ * β₂ := by nlinarith
  unfold velAdd
  rw [abs_div, abs_of_pos hD, div_lt_one hD, abs_lt]
  constructor <;> nlinarith

theorem W2p_LorentzFactor_boost_mul_boost (β₁ β₂ : ℝ) (h₁ : |β₁| < 1) (h₂ : |β₂| < 1) :
    boost β₁ * boost β₂ = boost (velAdd β₁ β₂) ∧
      gamma (velAdd β₁ β₂) = gamma β₁ * gamma β₂ * (1 + β₁ * β₂) ∧
      |velAdd β₁ β₂| < 1 := by
  obtain ⟨a1, a2⟩ := abs_lt.mp h₁
  obtain ⟨b1, b2⟩ := abs_lt.mp h₂
  have hD : 0 < 1 + β₁ * β₂ := by nlinarith
  have hD0 := hD.ne'
  have hD0' : 1 + β₂ * β₁ ≠ 0 := by rw [mul_comm]; exact hD0
  have ha1 := W2p_LorentzFactor_pos β₁ h₁
  have ha2 := W2p_LorentzFactor_pos β₂ h₂
  have hs1 : 0 < Real.sqrt (1 - β₁ ^ 2) := Real.sqrt_pos.mpr ha1
  have hs2 : 0 < Real.sqrt (1 - β₂ ^ 2) := Real.sqrt_pos.mpr ha2
  have hs1' := hs1.ne'
  have hs2' := hs2.ne'
  have hg : gamma (velAdd β₁ β₂) = gamma β₁ * gamma β₂ * (1 + β₁ * β₂) := by
    unfold gamma velAdd
    have e : 1 - ((β₁ + β₂) / (1 + β₁ * β₂)) ^ 2 =
        (1 - β₁ ^ 2) * (1 - β₂ ^ 2) / (1 + β₁ * β₂) ^ 2 := by
      field_simp <;> ring
    rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_mul ha1.le, Real.sqrt_sq hD.le]
    field_simp <;> ring
  refine ⟨?_, hg, W2p_LorentzFactor_velAdd_abs β₁ β₂ h₁ h₂⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boost, Matrix.mul_apply, Fin.sum_univ_two, hg] <;> (try unfold velAdd) <;>
    (try field_simp) <;> ring

theorem W2p_LorentzFactor_sqrt_one_sub_inv_gamma_sq (β : ℝ) (h₀ : 0 ≤ β) (h₁ : β < 1) :
    Real.sqrt (1 - 1 / gamma β ^ 2) = β := by
  have ha : 0 < 1 - β ^ 2 := by nlinarith
  unfold gamma
  rw [div_pow, one_pow, one_div_one_div, Real.sq_sqrt ha.le, sub_sub_cancel, Real.sqrt_sq h₀]

theorem W2p_LorentzFactor_gamma_values :
    gamma 0 = 1 ∧ gamma (3 / 5) = 5 / 4 ∧ gamma (4 / 5) = 5 / 3 ∧
      gamma (Real.sqrt 3 / 2) = 2 := by
  unfold gamma
  refine ⟨by simp, ?_, ?_, ?_⟩
  · rw [show (1 - (3 / 5 : ℝ) ^ 2) = (4 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  · rw [show (1 - (4 / 5 : ℝ) ^ 2) = (3 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  · rw [div_pow, Real.sq_sqrt (by norm_num),
      show (1 - (3 : ℝ) / 2 ^ 2) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num

theorem W2p_LorentzFactor_gamma_sub_one_div_sq_tendsto :
    Tendsto (fun β : ℝ => (gamma β - 1) / β ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 2)) := by
  have hcont : Continuous (fun β : ℝ => Real.sqrt (1 - β ^ 2)) := by fun_prop
  have hs : Tendsto (fun β : ℝ => Real.sqrt (1 - β ^ 2)) (𝓝 0) (𝓝 1) := by
    simpa using hcont.tendsto 0
  have hc : Tendsto (fun β : ℝ => 1 / (Real.sqrt (1 - β ^ 2) * (1 + Real.sqrt (1 - β ^ 2))))
      (𝓝 0) (𝓝 (1 / 2)) := by
    rw [show (1 / 2 : ℝ) = 1 / (1 * (1 + 1)) by norm_num]
    exact tendsto_const_nhds.div (hs.mul (tendsto_const_nhds.add hs)) (by norm_num)
  refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))]
    with β hβ hβ1
  have hβ' : β ≠ 0 := hβ
  obtain ⟨l1, l2⟩ := hβ1
  unfold gamma
  have hpos : 0 < 1 - β ^ 2 := by nlinarith
  set s := Real.sqrt (1 - β ^ 2) with hsdef
  have hs2 : s ^ 2 = 1 - β ^ 2 := Real.sq_sqrt hpos.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
  have hs1 : s ≠ 1 := by
    intro h1
    rw [h1] at hs2
    have hb : β ^ 2 = 0 := by nlinarith
    exact hβ' (pow_eq_zero_iff two_ne_zero |>.mp hb)
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have h1s' : 1 + s ≠ 0 := by positivity
  have hs0' := hs0.ne'
  rw [show β ^ 2 = (1 - s) * (1 + s) by linear_combination hs2]
  field_simp <;> ring

theorem W2p_LorentzFactor_gamma_of_momentum (β m p : ℝ) (hβ : |β| < 1) (hm : 0 < m)
    (hp : p = gamma β * m * β) :
    gamma β = Real.sqrt (1 + (p / m) ^ 2) := by
  have hγ2 := W2p_LorentzFactor_gamma_sq β hβ
  have hγpos := W2p_LorentzFactor_gamma_pos β hβ
  subst hp
  rw [mul_right_comm, mul_div_cancel_right₀ _ hm.ne',
    show 1 + (gamma β * β) ^ 2 = gamma β ^ 2 by linear_combination -hγ2,
    Real.sqrt_sq hγpos.le]

theorem W2p_LorentzFactor_velAdd_tanh (w₁ w₂ : ℝ) :
    velAdd (Real.tanh w₁) (Real.tanh w₂) = Real.tanh (w₁ + w₂) := by
  have h1 := Real.cosh_pos w₁
  have h2 := Real.cosh_pos w₂
  have h3 : Real.cosh w₁ * Real.cosh w₂ + Real.sinh w₁ * Real.sinh w₂ ≠ 0 := by
    rw [← Real.cosh_add]; exact (Real.cosh_pos _).ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  simp only [velAdd, Real.tanh_eq_sinh_div_cosh, Real.sinh_add, Real.cosh_add]
  field_simp <;> ring

theorem W2p_LorentzFactor_gamma_tanh (w : ℝ) :
    gamma (Real.tanh w) = Real.cosh w ∧
      gamma (Real.tanh w) * Real.tanh w = Real.sinh w := by
  have hc := Real.cosh_pos w
  have hc2 : Real.cosh w ^ 2 ≠ 0 := by positivity
  have h1 : gamma (Real.tanh w) = Real.cosh w := by
    unfold gamma
    rw [Real.tanh_eq_sinh_div_cosh, div_pow, one_sub_div hc2, Real.cosh_sq_sub_sinh_sq,
      Real.sqrt_div' _ (by positivity), Real.sqrt_one, Real.sqrt_sq hc.le, one_div_one_div]
  refine ⟨h1, ?_⟩
  rw [h1, Real.tanh_eq_sinh_div_cosh]
  have := hc.ne'
  field_simp <;> ring

theorem W2p_LorentzFactor_gamma_tendsto_atTop :
    Tendsto gamma (𝓝[<] (1 : ℝ)) atTop := by
  have h1 : Tendsto (fun v : ℝ => Real.sqrt (1 - v ^ 2)) (𝓝[<] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hcont : Continuous (fun v : ℝ => Real.sqrt (1 - v ^ 2)) := by fun_prop
      have := hcont.tendsto 1
      simp only [one_pow, sub_self, Real.sqrt_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with v hv
      obtain ⟨hv1, hv2⟩ := hv
      exact Set.mem_Ioi.mpr (Real.sqrt_pos.mpr (by nlinarith))
  have e : gamma = fun v => (Real.sqrt (1 - v ^ 2))⁻¹ := by
    funext v; simp [gamma]
  rw [e]
  exact tendsto_inv_nhdsGT_zero.comp h1

theorem W2p_LorentzFactor_gamma_strictMonoOn : StrictMonoOn gamma (Set.Ico (0 : ℝ) 1) := by
  intro a ha b hb hab
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  unfold gamma
  have hpb : 0 < 1 - b ^ 2 := by nlinarith
  exact one_div_lt_one_div_of_lt (Real.sqrt_pos.mpr hpb)
    (Real.sqrt_lt_sqrt hpb.le (by nlinarith))

theorem W2p_LorentzFactor_alpha_eq_inv_gamma (β : ℝ) (h : |β| < 1) :
    alpha β = (gamma β)⁻¹ ∧ gamma β * alpha β = 1 := by
  have ha := W2p_LorentzFactor_pos β h
  have hs : 0 < Real.sqrt (1 - β ^ 2) := Real.sqrt_pos.mpr ha
  unfold alpha gamma
  refine ⟨by rw [one_div, inv_inv], one_div_mul_cancel hs.ne'⟩

theorem W2p_LorentzFactor_gamma_ge_one (β : ℝ) (h : |β| < 1) :
    1 ≤ gamma β ∧ (gamma β = 1 ↔ β = 0) := by
  have ha := W2p_LorentzFactor_pos β h
  have hs : 0 < Real.sqrt (1 - β ^ 2) := Real.sqrt_pos.mpr ha
  have hs1 : Real.sqrt (1 - β ^ 2) ≤ 1 :=
    (Real.sqrt_le_sqrt (by nlinarith : 1 - β ^ 2 ≤ 1)).trans_eq Real.sqrt_one
  refine ⟨by unfold gamma; exact one_le_one_div hs hs1, ?_⟩
  constructor
  · intro h1
    unfold gamma at h1
    rw [div_eq_one_iff_eq hs.ne'] at h1
    have h2 := Real.sq_sqrt ha.le
    rw [← h1] at h2
    have hb : β ^ 2 = 0 := by nlinarith
    exact pow_eq_zero_iff two_ne_zero |>.mp hb
  · rintro rfl
    simp [gamma]

theorem solution : StrictMonoOn gamma (Set.Ico (0 : ℝ) 1) := by
  apply W2p_LorentzFactor_gamma_strictMonoOn <;> assumption
