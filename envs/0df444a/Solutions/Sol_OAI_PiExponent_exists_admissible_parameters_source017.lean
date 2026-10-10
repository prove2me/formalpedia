-- Prove2me | solution 1 for OAI.PiExponent.exists_admissible_parameters_source017
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T13:46:36.295769+00:00
-- url     : https://prove2.me/submissions/6498ced8-b768-42b7-b33b-051abf9db3e5

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_AdmissibleParameters
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_WeightSeparation
import Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_Dimension
import Theorems.Thm_OAI_PiExponent_exists_uniform_weight_error_margin
import Theorems.Thm_OAI_PiExponent_exists_minimum_weight
import Theorems.Thm_OAI_PiExponent_exists_dimension_margin
import Theorems.Thm_OAI_PiExponent_exists_normalized_successive_approximations
import Theorems.Thm_OAI_PiExponent_exists_parameters
import Theorems.Thm_OAI_PiExponent_exists_small_rational_sigma
import Mathlib

namespace OAI
namespace PiExponent

noncomputable section
open Filter
open scoped Topology

theorem dimensionK_one_le (C : ℝ) (hC : 1 ≤ C) (m : ℕ) :
    1 ≤ dimensionK C m := by
  exact (Nat.one_le_floor_iff _).2 (one_le_pow₀ hC)

theorem dimensionW_pos (B : ℝ) (hB : 0 < B) (m : ℕ) :
    0 < dimensionW B m := by
  exact inv_pos.mpr (pow_pos hB m)

theorem dimensionV_pos (theta B C : ℝ) (htheta : 0 < theta)
    (hB : 0 < B) (hC : 1 ≤ C) (m : ℕ) :
    0 < dimensionV theta B C m := by
  have hK : 0 < (dimensionK C m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (dimensionK_one_le C hC m))
  exact mul_pos (mul_pos (mul_pos (by norm_num) hK) (pow_pos htheta m))
    (dimensionW_pos B hB m)

theorem dimension_volume (theta B C : ℝ) (htheta : 0 < theta)
    (hB : 0 < B) (hC : 1 ≤ C) (m : ℕ) :
    (dimensionK C m : ℝ) * (dimensionW B m / dimensionV theta B C m) *
      theta ^ m = 1 / 2 := by
  have hK : (dimensionK C m : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one (dimensionK_one_le C hC m)))
  have ht : theta ^ m ≠ 0 := ne_of_gt (pow_pos htheta m)
  have hw : dimensionW B m ≠ 0 := ne_of_gt (dimensionW_pos B hB m)
  unfold dimensionV
  field_simp

theorem dimension_volume_lt_one (theta C : ℝ) (htheta : 0 < theta)
    (hC : 0 ≤ C) (hsmall : C * theta < 1) (m : ℕ) (hm : 1 ≤ m) :
    (dimensionK C m : ℝ) * theta ^ m < 1 := by
  calc
    (dimensionK C m : ℝ) * theta ^ m ≤ C ^ m * theta ^ m :=
      mul_le_mul_of_nonneg_right (dimensionK_le C hC m) (pow_pos htheta m).le
    _ = (C * theta) ^ m := (mul_pow _ _ _).symm
    _ < 1 := pow_lt_one₀ (mul_nonneg hC htheta.le) hsmall (by omega)

theorem dimension_collision_identity (theta A B C eta : ℝ)
    (htheta : 0 < theta) (hA : 0 < A) (hB : 0 < B) (hC : 1 ≤ C) (m : ℕ) :
    eta ^ 2 * (dimensionK C m : ℝ) * theta ^ m /
        (((m : ℝ) + 1) * dimensionV theta B C m * A ^ m) =
      eta ^ 2 * (B / A) ^ m / (2 * ((m : ℝ) + 1)) := by
  have hK : (dimensionK C m : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one (dimensionK_one_le C hC m)))
  have ht : theta ^ m ≠ 0 := ne_of_gt (pow_pos htheta m)
  have hA' : A ^ m ≠ 0 := ne_of_gt (pow_pos hA m)
  have hB' : B ^ m ≠ 0 := ne_of_gt (pow_pos hB m)
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  unfold dimensionV dimensionW
  rw [div_pow]
  field_simp

end

theorem interpolationSeparationConstant_pos (m : ℕ) (sigma : ℚ)
    (hsigma : 0 < (sigma : ℝ)) : 0 < interpolationSeparationConstant m sigma := by
  unfold interpolationSeparationConstant
  positivity

theorem weightErrorCoefficient_nonneg (nu theta : ℝ) (K : ℕ)
    (hnu : 0 < nu) (htheta : 0 < theta) (hK : 1 ≤ K) :
    0 ≤ weightErrorCoefficient nu theta K := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h2K : 0 ≤ Real.log (2 * (K : ℝ)) := Real.log_nonneg (by linarith)
  have h200K : 0 ≤ Real.log (200 * (K : ℝ)) := Real.log_nonneg (by linarith)
  unfold weightErrorCoefficient
  linarith

theorem exists_initial_scale (nu theta epsilon : ℝ) (_htheta : 0 < theta)
    (hepsilon : 0 < epsilon) :
    ∃ F0 : ℝ, 0 < F0 ∧ 2 / theta < F0 ∧ nu / F0 < epsilon / 3 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (max (2 / theta) (3 * nu / epsilon)))
  have hF : 1 < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  have hthetaF : 2 / theta < (N : ℝ) :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hN
  have hnuF : 3 * nu / epsilon < (N : ℝ) :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hN
  refine ⟨N, by linarith, hthetaF, ?_⟩
  apply (div_lt_iff₀ (show (0 : ℝ) < N by linarith)).2
  have := (div_lt_iff₀ hepsilon).mp hnuF
  nlinarith

end PiExponent
end OAI

namespace OAI
namespace PiExponent
namespace Parameters

variable {ν : ℝ} (p : Parameters ν)

theorem B_pos : 0 < (p.B : ℝ) := lt_trans p.A_pos p.A_lt_B

theorem C_pos : 0 < (p.C : ℝ) := lt_trans zero_lt_one p.one_lt_C

theorem A_lt_one : (p.A : ℝ) < 1 := lt_trans p.A_lt_B p.B_lt_one

theorem theta_lt_one : (p.theta : ℝ) < 1 := lt_trans p.theta_lt_A p.A_lt_one

theorem CB_lt_one : (p.C : ℝ) * p.B < 1 := by
  have h := (lt_div_iff₀ p.C_pos).mp p.B_lt_inv_C
  simpa only [mul_comm] using h

theorem one_lt_C_theta_div_B : 1 < (p.C : ℝ) * p.theta / p.B := by
  apply (lt_div_iff₀ p.B_pos).2
  simpa using p.B_lt_C_theta

theorem one_lt_B_div_A : 1 < (p.B : ℝ) / p.A := by
  apply (lt_div_iff₀ p.A_pos).2
  simpa using p.A_lt_B

end Parameters
end PiExponent
end OAI

open OAI.PiExponent

theorem solution
    (nu Lambda c : ℝ) (hnu : 2 < nu) (hLambda : 0 < Lambda) (hc : 0 < c)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    Nonempty (AdmissibleParameters nu Lambda c) := by
  classical
  obtain ⟨P⟩ := OAI.PiExponent.exists_parameters nu hnu
  let g : ℝ := nu * ((P.A : ℝ) * (1 - P.eta) - P.theta) - (1 - P.theta)
  have hg : 0 < g := P.gap_pos
  let epsilon : ℝ := min (g / 2) (1 / 2)
  have hepsilon : 0 < epsilon := lt_min (by positivity) (by norm_num)
  have hepsg : epsilon < g := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hepshalf : epsilon ≤ 1 / 2 := min_le_right _ _
  have heps3 : 0 < epsilon / 3 := by positivity
  obtain ⟨F0, hF0, hFtheta, hFmargin⟩ :=
    exists_initial_scale nu P.theta epsilon P.theta_pos hepsilon
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨m, hm, hdim, hcollision⟩ := OAI.PiExponent.exists_dimension_margin
    P.theta P.A P.B P.C P.eta (Lambda * F0) (2 * Real.log 2)
    (epsilon / 3) (2 / c) P.theta_pos P.B_pos P.one_lt_C
    P.CB_lt_one P.one_lt_C_theta_div_B P.one_lt_B_div_A P.eta_pos
    (mul_pos hLambda hF0).le (by positivity) heps3
  let K : ℕ := dimensionK P.C m
  let w0 : ℚ := (P.B ^ m)⁻¹
  let v0 : ℚ := 2 * (K : ℚ) * P.theta ^ m * w0
  have hK : 1 ≤ K := dimensionK_one_le P.C P.one_lt_C.le m
  have hw0eq : (w0 : ℝ) = dimensionW P.B m := by simp [w0, dimensionW]
  have hv0eq : (v0 : ℝ) = dimensionV P.theta P.B P.C m := by
    simp [v0, dimensionV, K, hw0eq]
  have hw0 : 0 < (w0 : ℝ) := by
    rw [hw0eq]
    exact dimensionW_pos P.B P.B_pos m
  have hv0 : 0 < (v0 : ℝ) := by
    rw [hv0eq]
    exact dimensionV_pos P.theta P.B P.C P.theta_pos P.B_pos P.one_lt_C.le m
  have hvolume : (K : ℝ) * ((w0 : ℝ) / v0) * (P.theta : ℝ) ^ m = 1 / 2 := by
    rw [hw0eq, hv0eq]
    exact dimension_volume P.theta P.B P.C P.theta_pos P.B_pos P.one_lt_C.le m
  have hvolume1 : (K : ℝ) * (P.theta : ℝ) ^ m < 1 :=
    dimension_volume_lt_one P.theta P.C P.theta_pos P.C_pos.le P.C_theta_lt_one m hm
  have hcollision' : 2 < c *
      (P.eta ^ 2 * (K : ℝ) * (P.theta : ℝ) ^ m /
        (((m : ℝ) + 1) * (v0 : ℝ) * (P.A : ℝ) ^ m)) := by
    rw [hv0eq]
    change 2 < c * (P.eta ^ 2 * (dimensionK (P.C : ℝ) m : ℝ) *
      (P.theta : ℝ) ^ m / (((m : ℝ) + 1) *
        dimensionV (P.theta : ℝ) P.B P.C m * (P.A : ℝ) ^ m))
    rw [dimension_collision_identity P.theta P.A P.B P.C P.eta
      P.theta_pos P.A_pos P.B_pos P.one_lt_C.le]
    have hh := (div_lt_iff₀ hc).mp hcollision
    nlinarith
  obtain ⟨sigma, hsigma, hsigmaVol, hsigmaK, hsigmaTheta⟩ :=
    OAI.PiExponent.exists_small_rational_sigma m (1 / 2)
      ((K : ℝ) * (P.theta : ℝ) ^ m) P.theta (by norm_num) hvolume1 P.theta_lt_one
  have hnupos : 0 < nu := by linarith
  have hS : 0 ≤ weightErrorCoefficient nu P.theta K :=
    weightErrorCoefficient_nonneg nu P.theta K hnupos P.theta_pos hK
  obtain ⟨X, hX, hXmargin⟩ := OAI.PiExponent.exists_uniform_weight_error_margin m Lambda
    (weightErrorCoefficient nu P.theta K) (epsilon / 3) hLambda hS heps3
  obtain ⟨p, q, x, hx0, hxlog, happ, hx1, hgrowth⟩ :=
    OAI.PiExponent.exists_normalized_successive_approximations nu X
      (OAI.PiExponentApprox.weightSeparationFactor m
        (interpolationSeparationConstant m sigma) w0 v0 P.theta) hnupos hbad
  obtain ⟨wstar, hwstarX, hwstarLower, hwstarAttained⟩ :=
    OAI.PiExponent.exists_minimum_weight m hm (fun i : Fin m => x (i.val + 1)) X
      (fun i => (happ i.val).2.2.2.2)
  have hwstar : 0 < wstar := lt_of_lt_of_le zero_lt_one (le_trans hX hwstarX.le)
  refine ⟨{
    base := P
    epsilon := epsilon
    F0 := F0
    m := m
    K := K
    w0 := w0
    v0 := v0
    sigma := sigma
    p := p
    q := q
    x := x
    wstar := wstar
    epsilon_pos := hepsilon
    epsilon_lt_gap := hepsg
    epsilon_le_half := hepshalf
    F0_pos := hF0
    F0_large := hFtheta
    initial_margin := hFmargin
    m_pos := hm
    K_eq := rfl
    K_pos := hK
    w0_eq := hw0eq
    v0_eq := hv0eq
    w0_pos := hw0
    v0_pos := hv0
    volume_eq := hvolume
    volume_lt_one := hvolume1
    dimension_margin := ?_
    collision_margin := hcollision'
    sigma_pos := hsigma
    sigma_volume := ?_
    sigma_centers := hsigmaK
    sigma_theta := hsigmaTheta
    x_zero := hx0
    x_log := hxlog
    approximations := fun n => ⟨(happ n).1, (happ n).2.1, (happ n).2.2.1⟩
    x_one_le := hx1
    weight_growth := fun i hi _ => hgrowth i hi
    wstar_pos := hwstar
    wstar_lower := hwstarLower
    wstar_attained := hwstarAttained
    weight_margin := hXmargin wstar (fun i : Fin m => x (i.val + 1))
      hwstarX hwstarLower
  }⟩
  · rw [hv0eq, hw0eq]
    exact hdim
  · rw [hvolume]
    exact hsigmaVol

#print axioms solution
