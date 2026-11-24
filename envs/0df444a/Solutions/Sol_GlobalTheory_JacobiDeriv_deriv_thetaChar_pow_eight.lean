-- Prove2me | solution 1 for GlobalTheory.JacobiDeriv.deriv_thetaChar_pow_eight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:36:21.225191+00:00
-- url     : https://prove2.me/submissions/6d6bc1c9-a794-410e-a738-161e70b420fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DifferentiableAtDerivAtZero
import Theorems.Thm_GlobalTheory_JacobiDeriv_thetaChar_half_half
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Complex Filter ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology Real
namespace GlobalTheory.JacobiDeriv
open Complex Filter in
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology Real in
private lemma deriv_thetaChar_half_half' (τ : ℍ) :
    deriv (fun z : ℂ => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar (g := 1) !![(τ : ℂ)] ![1 / 2] ![1 / 2] ![z]) 0 =
      cexp (π * I * ((τ : ℂ) / 4 + 1 / 2)) * _root_.GlobalTheory.JacobiDeriv.derivAtZero τ := by
  simp_rw [_root_.GlobalTheory.JacobiDeriv.thetaChar_half_half]
  have hθ : HasDerivAt (fun z : ℂ => jacobiTheta₂ (z + ((τ : ℂ) + 1) / 2) τ)
      (jacobiTheta₂' (0 + ((τ : ℂ) + 1) / 2) τ) 0 :=
    (hasDerivAt_jacobiTheta₂_fst _ τ.im_pos).comp_add_const _ _
  have he : HasDerivAt (fun z : ℂ => cexp (π * I * ((τ : ℂ) / 4 + z + 1 / 2)))
      (cexp (π * I * ((τ : ℂ) / 4 + 0 + 1 / 2)) * (π * I)) 0 := by
    have h := ((((hasDerivAt_id (0 : ℂ)).const_add ((τ : ℂ) / 4)).add_const (1 / 2)).const_mul
      (π * I)).cexp
    simpa using h
  refine (HasDerivAt.deriv (he.mul hθ)).trans ?_
  simp only [zero_add, add_zero, _root_.GlobalTheory.JacobiDeriv.jacobiTheta₂_half_period]
  unfold _root_.GlobalTheory.JacobiDeriv.derivAtZero
  ring
open Complex Filter in
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology Real in
private lemma deriv_thetaChar_pow_eight_eq (τ : ℍ) :
    (deriv (fun z : ℂ => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar (g := 1) !![(τ : ℂ)] ![1 / 2] ![1 / 2] ![z]) 0) ^ 8 =
      _root_.GlobalTheory.JacobiDeriv.eighthPower τ := by
  rw [deriv_thetaChar_half_half', mul_pow, _root_.GlobalTheory.JacobiDeriv.eighthPower, ← Complex.exp_nat_mul]
  congr 1
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨2, ?_⟩
  push_cast
  ring
end GlobalTheory.JacobiDeriv
end
end

set_option autoImplicit false
noncomputable section
open Complex Filter ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology Real
open GlobalTheory GlobalTheory.JacobiDeriv
open Complex Filter
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology Real
namespace GlobalTheory.JacobiDeriv
namespace _root_.GlobalTheory.JacobiDeriv
theorem _root_.solution : ∀ τ : UpperHalfPlane,
    (deriv (fun z : ℂ => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar (g := 1) !![(τ : ℂ)] ![1 / 2] ![1 / 2] ![z]) 0) ^ 8 =
      (2 * Real.pi : ℂ) ^ 8 * ModularForm.discriminant τ := by
  have hΔ : CuspForm.discriminant ≠ 0 := by
    intro h
    have := congrArg (fun f : CuspForm 𝒮ℒ 12 => f UpperHalfPlane.I) h
    exact ModularForm.discriminant_ne_zero UpperHalfPlane.I (by simpa using this)
  have hrank : Module.finrank ℂ (CuspForm 𝒮ℒ 12) = 1 :=
    Module.finrank_eq_of_rank_eq CuspForm.rank_eq_one_of_weight_eq_twelve
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hΔ).mp hrank
    _root_.GlobalTheory.JacobiDeriv.eighthPowerForm
  have hpt : ∀ τ : ℍ, _root_.GlobalTheory.JacobiDeriv.eighthPower τ = c * ModularForm.discriminant τ := by
    intro τ
    have := congrArg (fun f : CuspForm 𝒮ℒ 12 => f τ) hc
    have h2 : _root_.GlobalTheory.JacobiDeriv.eighthPowerForm τ = c * ModularForm.discriminant τ := by
      simpa using this.symm
    exact h2
  have hD : ∀ τ : ℍ, _root_.GlobalTheory.JacobiDeriv.derivAtZero τ ^ 8 =
      c * ∏' n : ℕ, (1 - ModularForm.eta_q n τ) ^ 24 := by
    intro τ
    have h := hpt τ
    rw [ModularForm.discriminant_eq_q_prod, _root_.GlobalTheory.JacobiDeriv.qParam_one,
      _root_.GlobalTheory.JacobiDeriv.eighthPower] at h
    have hq : cexp (2 * π * I * τ) ≠ 0 := Complex.exp_ne_zero _
    apply mul_left_cancel₀ hq
    rw [h]; ring
  have hlim1 := _root_.GlobalTheory.JacobiDeriv.tendsto_derivAtZero.pow 8
  have hlim2 := ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow.const_mul c
  have hc' : (2 * π * I) ^ 8 = c * 1 :=
    tendsto_nhds_unique hlim1 (hlim2.congr fun τ => (hD τ).symm)
  intro τ
  rw [deriv_thetaChar_pow_eight_eq, hpt, mul_one] at *
  rw [← hc']
  have hI : I ^ 8 = 1 := by
    rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, I_pow_four, one_pow]
  rw [mul_pow, mul_pow, hI, mul_one]
end _root_.GlobalTheory.JacobiDeriv
end GlobalTheory.JacobiDeriv
