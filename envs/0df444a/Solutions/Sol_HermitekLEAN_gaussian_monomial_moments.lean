-- Prove2me | solution 1 for HermitekLEAN.gaussian_monomial_moments
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:19.718663+00:00
-- url     : https://prove2.me/submissions/35147993-67a2-4c28-80d2-cee088d6b2f7

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
namespace HermitekLEAN
private lemma gaussian_monomial_moments_off_diag {a b : ℕ} (hab : a ≠ b) :
    ∫ z : ℂ, ((z ^ a) * (star z) ^ b).re * Real.exp (-‖z‖ ^ 2) = 0 := by
  -- Rotation trick: pick ω on the unit circle s.t. ω^(a-b) = -1, then I = -I.
  set d : ℤ := (a : ℤ) - (b : ℤ) with hd_def
  have hd_ne : (d : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr (by exact_mod_cast hab)
  set ω : _root_.Circle := _root_.Circle.exp (Real.pi / (d : ℝ))
  -- Key: ω^a * conj(ω)^b = -1
  have hω_factor : ((ω : ℂ) ^ a * star (ω : ℂ) ^ b) = -1 := by
    rw [star_def, ← _root_.Circle.coe_inv_eq_conj,
      ← _root_.Circle.coe_pow, ← _root_.Circle.coe_pow, ← _root_.Circle.coe_mul]
    -- Goal: ↑(ω^a * ω⁻¹^b) = -1. Reduce ω^a * ω⁻¹^b to ω^d.
    have hprod : ω ^ a * ω⁻¹ ^ b = ω ^ d := by
      rw [hd_def]
      rw [show ω ^ a * ω⁻¹ ^ b = ω ^ a * (ω ^ b)⁻¹ from by rw [inv_pow]]
      rw [← zpow_natCast ω a, ← zpow_natCast ω b, ← zpow_sub]
    rw [hprod]
    -- ω^d = Circle.exp(π/d)^d = Circle.exp(d * (π/d)) = Circle.exp(π) = -1
    rw [show ω = _root_.Circle.exp (Real.pi / (d : ℝ)) from rfl,
      ← _root_.Circle.exp_intCast_mul (Real.pi / (d : ℝ)) d,
      show (d : ℝ) * (Real.pi / (d : ℝ)) = Real.pi from by field_simp]
    simp [_root_.Circle.coe_exp, Complex.exp_pi_mul_I]
  -- The rotation ω preserves the measure
  set rot : ℂ ≃ₗᵢ[ℝ] ℂ := rotation ω
  have hmp := rot.measurePreserving
  have hemb : MeasurableEmbedding (⇑rot) :=
    rot.toHomeomorph.measurableEmbedding
  -- Express the integral after rotation
  have hI : ∀ z : ℂ,
      ((rot z) ^ a * star (rot z) ^ b).re * Real.exp (-‖rot z‖ ^ 2) =
      -((z ^ a * star z ^ b).re * Real.exp (-‖z‖ ^ 2)) := by
    intro z
    simp only [rot, rotation_apply, mul_pow, star_mul]
    rw [norm_mul, _root_.Circle.norm_coe, one_mul]
    have : (↑ω ^ a * z ^ a * (star z ^ b * star ↑ω ^ b)).re =
        ((↑ω ^ a * star ↑ω ^ b) * (z ^ a * star z ^ b)).re := by ring_nf
    rw [this, hω_factor]
    simp only [Complex.neg_re, Complex.mul_re, neg_mul, one_mul,
      neg_sub]
    ring
  -- Apply rotation to the integral: ∫ f(rot z) dz = ∫ f(z) dz
  set f : ℂ → ℝ := fun z => (z ^ a * star z ^ b).re * Real.exp (-‖z‖ ^ 2) with hf_def
  have hrot_eq : ∫ z, f (rot z) = ∫ z, f z :=
    hmp.integral_comp hemb f
  -- But f(rot z) = -f(z), so ∫ -f = ∫ f, hence ∫ f = 0
  have hrot_neg : ∀ z, f (rot z) = -f z := hI
  simp_rw [hrot_neg] at hrot_eq
  rw [integral_neg] at hrot_eq
  linarith only [hrot_eq]
private lemma zpow_conj_diag_re (z : ℂ) (a : ℕ) :
    (z ^ a * (starRingEnd ℂ) z ^ a).re = ‖z‖ ^ (2 * a) := by
  rw [← mul_pow, Complex.mul_conj']
  norm_cast
  rw [← pow_mul]
private lemma integral_norm_pow_exp_gaussian (a : ℕ) :
    ∫ z : ℂ, ‖z‖ ^ (2 * a) * Real.exp (-‖z‖ ^ 2) = π * (Nat.factorial a : ℝ) := by
  have h_rpow : ∀ z : ℂ, (‖z‖ : ℝ) ^ (2 * a) = ‖z‖ ^ ((2 * a : ℕ) : ℝ) := by
    intro z; exact (rpow_natCast ‖z‖ (2 * a)).symm
  have h_exp : ∀ z : ℂ, Real.exp (-‖z‖ ^ 2) = Real.exp (-‖z‖ ^ (2 : ℝ)) := by intro z; norm_num
  simp_rw [h_rpow, h_exp]
  rw [Complex.integral_rpow_mul_exp_neg_rpow (show (1 : ℝ) ≤ 2 from by linarith only [])
    (show (-2 : ℝ) < ((2 * a : ℕ) : ℝ) from by
      have : (0 : ℝ) ≤ ((2 * a : ℕ) : ℝ) := Nat.cast_nonneg _; linarith only [])]
  rw [show ((2 * a : ℕ) : ℝ) + 2 = 2 * ((a : ℝ) + 1) from by push_cast; ring,
    show 2 * ((a : ℝ) + 1) / 2 = (a : ℝ) + 1 from by ring,
    show 2 * π / 2 = π from by ring,
    Real.Gamma_nat_eq_factorial]
end HermitekLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ (a b : ℕ),
      (1 / Real.pi) *
          ∫ z : ℂ, ((z ^ a) * (star z) ^ b).re * Real.exp (-‖z‖ ^ 2)
        = if a = b then (Nat.factorial a : ℝ) else 0 := by
  intro a b
  by_cases hab : a = b
  · -- Diagonal case: a = b
    subst hab
    rw [if_pos rfl]
    have hre : ∀ z : ℂ, (z ^ a * star z ^ a).re * Real.exp (-‖z‖ ^ 2) =
        ‖z‖ ^ (2 * a) * Real.exp (-‖z‖ ^ 2) := by
      intro z; rw [show star z = (starRingEnd ℂ) z from rfl, zpow_conj_diag_re]
    simp_rw [hre]; rw [integral_norm_pow_exp_gaussian]
    rw [show (1 : ℝ) / π * (π * ↑(Nat.factorial a)) = ↑(Nat.factorial a) from by field_simp]
  · -- Off-diagonal case: a ≠ b
    rw [if_neg hab, gaussian_monomial_moments_off_diag hab, mul_zero]
end HermitekLEAN
