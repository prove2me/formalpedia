-- Prove2me | solution 1 for LambdaCDM.scaleFactor_strictMonoOn_and_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T19:25:15.48031+00:00
-- url     : https://prove2.me/submissions/aa0f95ed-c044-4383-a168-c0671e87363f

import Mathlib
import Definitions.Def_FlatLambdaCDM
import Definitions.Def_FRWUniverse

open LambdaCDM

theorem W2c_LambdaCDM_theta_pos (P : FlatLCDM) (t : ℝ) (ht : 0 < t) : 0 < theta P t := by
  have h1 := Real.sqrt_pos.2 P.OL_pos
  have h2 := P.H0_pos
  unfold theta; positivity

theorem W2c_LambdaCDM_sinh_pos (P : FlatLCDM) (t : ℝ) (ht : 0 < t) :
    0 < Real.sinh (theta P t) :=
  Real.sinh_pos_iff.2 (W2c_LambdaCDM_theta_pos P t ht)

theorem W2c_LambdaCDM_sf_pos (P : FlatLCDM) (t : ℝ) (ht : 0 < t) : 0 < scaleFactor P t := by
  have hs := W2c_LambdaCDM_sinh_pos P t ht
  have hr : 0 < P.Om / P.OL := div_pos P.Om_pos P.OL_pos
  unfold scaleFactor
  exact mul_pos (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hs _)

theorem W2c_LambdaCDM_cube (P : FlatLCDM) (t : ℝ) (ht : 0 < t) :
    scaleFactor P t ^ 3 = P.Om / P.OL * Real.sinh (theta P t) ^ 2 := by
  have hs := W2c_LambdaCDM_sinh_pos P t ht
  have hr : 0 < P.Om / P.OL := div_pos P.Om_pos P.OL_pos
  unfold scaleFactor
  rw [mul_pow]
  have e1 : ((P.Om / P.OL) ^ ((1:ℝ) / 3)) ^ 3 = P.Om / P.OL := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; norm_num
  have e2 : (Real.sinh (theta P t) ^ ((2:ℝ) / 3)) ^ 3 = Real.sinh (theta P t) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]; norm_num
  rw [e1, e2]

theorem W2c_LambdaCDM_theta_hasDerivAt (P : FlatLCDM) (t : ℝ) :
    HasDerivAt (theta P) (3 / 2 * Real.sqrt P.OL * P.H0) t := by
  have h := (hasDerivAt_id' t).const_mul (3 / 2 * Real.sqrt P.OL * P.H0)
  rw [mul_one] at h
  exact h

theorem W2c_LambdaCDM_sf_hasDerivAt (P : FlatLCDM) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (scaleFactor P)
      (scaleFactor P t * (P.H0 * Real.sqrt P.OL *
        (Real.cosh (theta P t) / Real.sinh (theta P t)))) t := by
  have hs := W2c_LambdaCDM_sinh_pos P t ht
  have hθ := W2c_LambdaCDM_theta_hasDerivAt P t
  have h1 := (hθ.sinh.rpow_const (p := (2:ℝ) / 3) (Or.inl hs.ne')).const_mul
    ((P.Om / P.OL) ^ ((1:ℝ) / 3))
  have hfun : scaleFactor P = fun y =>
      (P.Om / P.OL) ^ ((1:ℝ) / 3) * Real.sinh (theta P y) ^ ((2:ℝ) / 3) := by
    funext y; rfl
  rw [hfun]
  refine h1.congr_deriv ?_
  rw [Real.rpow_sub_one hs.ne']
  field_simp

theorem W2c_LambdaCDM_scaleFactor_hasDerivAt (P : FlatLCDM) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (scaleFactor P)
      (scaleFactor P t * (P.H0 * Real.sqrt P.OL *
        (Real.cosh (theta P t) / Real.sinh (theta P t)))) t :=
  W2c_LambdaCDM_sf_hasDerivAt P t ht

theorem W2c_LambdaCDM_friedmann (P : FlatLCDM) (t : ℝ) (ht : 0 < t) :
    (deriv (scaleFactor P) t / scaleFactor P t) ^ 2
      = P.H0 ^ 2 * (P.Om / scaleFactor P t ^ 3 + P.OL) := by
  have hs := W2c_LambdaCDM_sinh_pos P t ht
  have ha := W2c_LambdaCDM_sf_pos P t ht
  have hOm := P.Om_pos
  have hOL := P.OL_pos
  rw [(W2c_LambdaCDM_sf_hasDerivAt P t ht).deriv, mul_div_cancel_left₀ _ ha.ne',
    W2c_LambdaCDM_cube P t ht, mul_pow, mul_pow, div_pow, Real.cosh_sq,
    Real.sq_sqrt hOL.le]
  field_simp
  ring

theorem W2c_LambdaCDM_theta_age (P : FlatLCDM) :
    theta P (age P) = Real.arsinh (Real.sqrt (P.OL / P.Om)) := by
  unfold theta age
  have h1 := Real.sqrt_pos.2 P.OL_pos
  have h2 := P.H0_pos
  field_simp
  try ring

theorem W2c_LambdaCDM_scaleFactor_age (P : FlatLCDM) : scaleFactor P (age P) = 1 := by
  have hOm := P.Om_pos
  have hOL := P.OL_pos
  unfold scaleFactor
  rw [W2c_LambdaCDM_theta_age, Real.sinh_arsinh, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (by positivity), show (1:ℝ) / 2 * (2 / 3) = 1 / 3 by norm_num,
    ← Real.mul_rpow (by positivity) (by positivity)]
  have : P.Om / P.OL * (P.OL / P.Om) = 1 := by field_simp
  rw [this, Real.one_rpow]

theorem W2c_LambdaCDM_age_pos (P : FlatLCDM) : 0 < age P := by
  have h1 := Real.sqrt_pos.2 P.OL_pos
  have h2 := P.H0_pos
  have h3 : 0 < Real.sqrt (P.OL / P.Om) := Real.sqrt_pos.2 (div_pos P.OL_pos P.Om_pos)
  unfold age
  exact mul_pos (by positivity) (Real.arsinh_pos_iff.2 h3)

theorem W2c_LambdaCDM_expansion_law (P : FlatLCDM) :
    (∀ t : ℝ, 0 < t → 0 < scaleFactor P t) ∧
    (∀ t : ℝ, 0 < t →
      (deriv (scaleFactor P) t / scaleFactor P t) ^ 2
        = P.H0 ^ 2 * (P.Om / scaleFactor P t ^ 3 + P.OL)) ∧
    0 < age P ∧ scaleFactor P (age P) = 1 :=
  ⟨W2c_LambdaCDM_sf_pos P, W2c_LambdaCDM_friedmann P, W2c_LambdaCDM_age_pos P,
    W2c_LambdaCDM_scaleFactor_age P⟩

theorem W2c_LambdaCDM_age_eq_log (P : FlatLCDM) :
    age P = 2 / (3 * P.H0 * Real.sqrt P.OL) *
      Real.log ((1 + Real.sqrt P.OL) / Real.sqrt P.Om) := by
  have hOm := P.Om_pos
  have hOL := P.OL_pos
  have hsOm := Real.sqrt_pos.2 hOm
  unfold age
  congr 1
  have e1 : Real.sqrt (P.OL / P.Om) = Real.sqrt P.OL / Real.sqrt P.Om := Real.sqrt_div hOL.le _
  have e2 : 1 + Real.sqrt (P.OL / P.Om) ^ 2 = 1 / P.Om := by
    rw [Real.sq_sqrt (div_pos hOL hOm).le]
    field_simp
    linarith [P.flat]
  rw [Real.arsinh, e2, e1, Real.sqrt_div' _ hOm.le, Real.sqrt_one]
  congr 1
  field_simp
  try ring

theorem W2c_LambdaCDM_mono_tendsto (P : FlatLCDM) :
    StrictMonoOn (scaleFactor P) (Set.Ioi 0) ∧
      Filter.Tendsto (scaleFactor P) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hr : 0 < P.Om / P.OL := div_pos P.Om_pos P.OL_pos
  have hc : 0 < (P.Om / P.OL) ^ ((1:ℝ) / 3) := Real.rpow_pos_of_pos hr _
  constructor
  · intro s hs t ht hst
    have hθ : theta P s < theta P t := by
      have h1 := Real.sqrt_pos.2 P.OL_pos
      have h2 := P.H0_pos
      unfold theta
      have : 0 < 3 / 2 * Real.sqrt P.OL * P.H0 := by positivity
      exact mul_lt_mul_of_pos_left hst this
    have hss := W2c_LambdaCDM_sinh_pos P s hs
    unfold scaleFactor
    apply mul_lt_mul_of_pos_left _ hc
    exact Real.rpow_lt_rpow hss.le (Real.sinh_strictMono hθ) (by norm_num)
  · have hcont : Continuous (scaleFactor P) := by
      have : scaleFactor P = fun t =>
          (P.Om / P.OL) ^ ((1:ℝ) / 3) *
            Real.sinh (3 / 2 * Real.sqrt P.OL * P.H0 * t) ^ ((2:ℝ) / 3) := by
        funext t; rfl
      rw [this]
      exact continuous_const.mul
        (Continuous.rpow_const (Real.continuous_sinh.comp (continuous_const.mul continuous_id))
          (fun _ => Or.inr (by norm_num)))
    have h0 : scaleFactor P 0 = 0 := by
      unfold scaleFactor theta
      rw [mul_zero, Real.sinh_zero, Real.zero_rpow (by norm_num), mul_zero]
    have := hcont.tendsto 0
    rw [h0] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this

/-- derivative of `a * (k * coth θ)` -/
theorem W2c_LambdaCDM_adot (P : FlatLCDM) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => scaleFactor P s * (P.H0 * Real.sqrt P.OL *
        (Real.cosh (theta P s) / Real.sinh (theta P s))))
      (scaleFactor P t * (P.H0 * Real.sqrt P.OL) *
        (P.H0 * Real.sqrt P.OL * Real.cosh (theta P t) ^ 2 -
          3 / 2 * Real.sqrt P.OL * P.H0 *
            (Real.cosh (theta P t) ^ 2 - Real.sinh (theta P t) ^ 2)) /
        Real.sinh (theta P t) ^ 2) t := by
  have hs := W2c_LambdaCDM_sinh_pos P t ht
  have hθ := W2c_LambdaCDM_theta_hasDerivAt P t
  have h1 := W2c_LambdaCDM_sf_hasDerivAt P t ht
  have h2 := ((hθ.cosh).div (hθ.sinh) hs.ne').const_mul (P.H0 * Real.sqrt P.OL)
  refine (h1.mul h2).congr_deriv ?_
  simp only [Pi.div_apply]
  field_simp
  ring

theorem W2c_LambdaCDM_dd (P : FlatLCDM) (t : ℝ) (ht : 0 < t) :
    deriv (deriv (scaleFactor P)) t = scaleFactor P t * (P.H0 ^ 2 * P.OL) *
      (Real.sinh (theta P t) ^ 2 - 1 / 2) / Real.sinh (theta P t) ^ 2 := by
  have hev : deriv (scaleFactor P) =ᶠ[nhds t] fun s => scaleFactor P s *
      (P.H0 * Real.sqrt P.OL * (Real.cosh (theta P s) / Real.sinh (theta P s))) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact (W2c_LambdaCDM_sf_hasDerivAt P s hs).deriv
  rw [hev.deriv_eq, (W2c_LambdaCDM_adot P t ht).deriv, Real.cosh_sq_sub_sinh_sq, Real.cosh_sq]
  rw [show P.H0 ^ 2 * P.OL = P.H0 ^ 2 * Real.sqrt P.OL ^ 2 by
    rw [Real.sq_sqrt P.OL_pos.le]]
  ring

theorem W2c_LambdaCDM_accel_pos_iff (P : FlatLCDM) (t : ℝ) (ht : 0 < t) :
    0 < deriv (deriv (scaleFactor P)) t ↔ P.Om < 2 * P.OL * scaleFactor P t ^ 3 := by
  rw [W2c_LambdaCDM_dd P t ht, W2c_LambdaCDM_cube P t ht]
  have hs := W2c_LambdaCDM_sinh_pos P t ht
  have ha := W2c_LambdaCDM_sf_pos P t ht
  have hOm := P.Om_pos
  have hOL := P.OL_pos
  have hH := P.H0_pos
  have hpos : 0 < scaleFactor P t * (P.H0 ^ 2 * P.OL) / Real.sinh (theta P t) ^ 2 := by
    positivity
  rw [show scaleFactor P t * (P.H0 ^ 2 * P.OL) * (Real.sinh (theta P t) ^ 2 - 1 / 2) /
      Real.sinh (theta P t) ^ 2 = scaleFactor P t * (P.H0 ^ 2 * P.OL) /
      Real.sinh (theta P t) ^ 2 * (Real.sinh (theta P t) ^ 2 - 1 / 2) by ring,
    mul_pos_iff_of_pos_left hpos]
  have : 2 * P.OL * (P.Om / P.OL * Real.sinh (theta P t) ^ 2) =
      2 * P.Om * Real.sinh (theta P t) ^ 2 := by field_simp; try ring
  rw [this]
  constructor
  · intro h; nlinarith [mul_pos hOm h]
  · intro h
    by_contra hc
    push_neg at hc
    nlinarith [mul_le_mul_of_nonneg_left hc hOm.le]

theorem W2c_LambdaCDM_accel_zero_iff (P : FlatLCDM) (t : ℝ) (ht : 0 < t) :
    deriv (deriv (scaleFactor P)) t = 0 ↔ scaleFactor P t ^ 3 = P.Om / (2 * P.OL) := by
  rw [W2c_LambdaCDM_dd P t ht, W2c_LambdaCDM_cube P t ht]
  have hs := W2c_LambdaCDM_sinh_pos P t ht
  have ha := W2c_LambdaCDM_sf_pos P t ht
  have hOm := P.Om_pos
  have hOL := P.OL_pos
  have hH := P.H0_pos
  have hpos : 0 < scaleFactor P t * (P.H0 ^ 2 * P.OL) / Real.sinh (theta P t) ^ 2 := by
    positivity
  rw [show scaleFactor P t * (P.H0 ^ 2 * P.OL) * (Real.sinh (theta P t) ^ 2 - 1 / 2) /
      Real.sinh (theta P t) ^ 2 = scaleFactor P t * (P.H0 ^ 2 * P.OL) /
      Real.sinh (theta P t) ^ 2 * (Real.sinh (theta P t) ^ 2 - 1 / 2) by ring,
    mul_eq_zero]
  have hr : P.Om / P.OL ≠ 0 := (div_pos hOm hOL).ne'
  constructor
  · rintro (h | h)
    · exact absurd h hpos.ne'
    · have h2 : Real.sinh (theta P t) ^ 2 = 1 / 2 := by linarith
      rw [h2]; ring
  · intro h
    right
    have h2 : P.Om / P.OL * (Real.sinh (theta P t) ^ 2 - 1 / 2) = 0 := by
      linear_combination h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hr
    · exact h3

theorem W2c_LambdaCDM_exists_frw (P : FlatLCDM) (G : ℝ) (hG : 0 < G) :
    ∃ U : FRWCosmology.FRWUniverse,
      U.G = G ∧ U.K = 0 ∧ U.I = Set.Ioi 0 ∧ U.a = scaleFactor P ∧
      (∀ t ∈ U.I, U.rho t = 3 * P.H0 ^ 2 / (8 * Real.pi * G) *
        (P.Om / scaleFactor P t ^ 3 + P.OL)) ∧
      (∀ t ∈ U.I, U.p t = -(3 * P.H0 ^ 2 / (8 * Real.pi * G)) * P.OL) := by
  have hOm := P.Om_pos
  have hOL := P.OL_pos
  have hH := P.H0_pos
  have hπ := Real.pi_pos
  have hπ' := Real.pi_ne_zero
  have hG' := hG.ne'
  have hsOL := Real.sqrt_pos.2 hOL
  have hsq : Real.sqrt P.OL ^ 2 = P.OL := Real.sq_sqrt hOL.le
  let rho : ℝ → ℝ := fun t => 3 * P.H0 ^ 2 / (8 * Real.pi * G) *
    (P.Om / scaleFactor P t ^ 3 + P.OL)
  have hrho : ∀ t ∈ Set.Ioi (0:ℝ), HasDerivAt rho (deriv rho t) t := by
    intro t ht
    have ha := W2c_LambdaCDM_sf_pos P t ht
    have hd := (W2c_LambdaCDM_sf_hasDerivAt P t ht).differentiableAt
    exact ((((differentiableAt_const P.Om).div (hd.pow 3)
      (pow_ne_zero 3 ha.ne')).add_const P.OL).const_mul _).hasDerivAt
  have hf1 : ∀ t ∈ Set.Ioi (0:ℝ),
      (scaleFactor P t * (P.H0 * Real.sqrt P.OL *
        (Real.cosh (theta P t) / Real.sinh (theta P t))) / scaleFactor P t) ^ 2
        = 8 * Real.pi * G / 3 * rho t - 0 / scaleFactor P t ^ 2 := by
    intro t ht
    have ha := W2c_LambdaCDM_sf_pos P t ht
    have hs := W2c_LambdaCDM_sinh_pos P t ht
    show _ = 8 * Real.pi * G / 3 * (3 * P.H0 ^ 2 / (8 * Real.pi * G) *
      (P.Om / scaleFactor P t ^ 3 + P.OL)) - 0 / scaleFactor P t ^ 2
    rw [mul_div_cancel_left₀ _ ha.ne', W2c_LambdaCDM_cube P t ht, mul_pow, mul_pow, div_pow,
      Real.cosh_sq, hsq]
    field_simp
    ring
  have hf2 : ∀ t ∈ Set.Ioi (0:ℝ),
      scaleFactor P t * (P.H0 * Real.sqrt P.OL) *
        (P.H0 * Real.sqrt P.OL * Real.cosh (theta P t) ^ 2 -
          3 / 2 * Real.sqrt P.OL * P.H0 *
            (Real.cosh (theta P t) ^ 2 - Real.sinh (theta P t) ^ 2)) /
        Real.sinh (theta P t) ^ 2 / scaleFactor P t -
      (scaleFactor P t * (P.H0 * Real.sqrt P.OL *
        (Real.cosh (theta P t) / Real.sinh (theta P t))) / scaleFactor P t) ^ 2
        = -(4 * Real.pi * G) * (rho t + -(3 * P.H0 ^ 2 / (8 * Real.pi * G)) * P.OL)
          + 0 / scaleFactor P t ^ 2 := by
    intro t ht
    have ha := W2c_LambdaCDM_sf_pos P t ht
    have hs := W2c_LambdaCDM_sinh_pos P t ht
    show _ = -(4 * Real.pi * G) * (3 * P.H0 ^ 2 / (8 * Real.pi * G) *
      (P.Om / scaleFactor P t ^ 3 + P.OL) + -(3 * P.H0 ^ 2 / (8 * Real.pi * G)) * P.OL)
          + 0 / scaleFactor P t ^ 2
    rw [mul_div_cancel_left₀ _ ha.ne', W2c_LambdaCDM_cube P t ht, mul_pow, mul_pow, div_pow,
      Real.cosh_sq_sub_sinh_sq, Real.cosh_sq]
    have hsOL' := hsOL
    generalize Real.sqrt P.OL = r at hsq hsOL' ⊢
    rw [← hsq]
    field_simp
    ring
  refine ⟨⟨G, 0, Set.Ioi 0, scaleFactor P,
    fun t => scaleFactor P t * (P.H0 * Real.sqrt P.OL *
        (Real.cosh (theta P t) / Real.sinh (theta P t))),
    fun t => scaleFactor P t * (P.H0 * Real.sqrt P.OL) *
        (P.H0 * Real.sqrt P.OL * Real.cosh (theta P t) ^ 2 -
          3 / 2 * Real.sqrt P.OL * P.H0 *
            (Real.cosh (theta P t) ^ 2 - Real.sinh (theta P t) ^ 2)) /
        Real.sinh (theta P t) ^ 2,
    rho, deriv rho, fun _ => -(3 * P.H0 ^ 2 / (8 * Real.pi * G)) * P.OL,
    isOpen_Ioi, isPreconnected_Ioi, fun t ht => W2c_LambdaCDM_sf_pos P t ht,
    fun t ht => W2c_LambdaCDM_sf_hasDerivAt P t ht, fun t ht => W2c_LambdaCDM_adot P t ht,
    hrho, hf1, hf2⟩, rfl, rfl, rfl, rfl,
    fun t _ => rfl, fun t _ => rfl⟩

theorem solution (P : FlatLCDM) :
    StrictMonoOn (scaleFactor P) (Set.Ioi 0) ∧
      Filter.Tendsto (scaleFactor P) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  apply W2c_LambdaCDM_mono_tendsto <;> assumption
