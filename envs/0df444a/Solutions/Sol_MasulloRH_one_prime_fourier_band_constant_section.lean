-- Prove2me | solution 1 for MasulloRH.one_prime_fourier_band_constant_section
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-22T21:23:51.188426+00:00
-- url     : https://prove2.me/submissions/21f57d31-7f0f-443b-81b7-c4b5130e46f0

import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Module

/- Source module: MasulloLocal/NormalizedBump.lean -/
/-!
# An actual even normalized Fourier-side bump

For every positive bandwidth, a normalized bump centered at X/2 is supported
inside (X/4, 3X/4). The half-sum of this bump and its reflection is a complex
Schwartz function with integral one, even symmetry, and zero value at the origin.
No existence or normalization hypothesis is taken as an input.
-/

open scoped SchwartzMap FourierTransform ContDiff
open MeasureTheory

set_option autoImplicit false

noncomputable section

namespace MasulloLocal

/-- The positive-side bump uses radii X/8 and X/4 around X/2. -/
def positiveBandBumpShape {X : ℝ} (hX : 0 < X) : ContDiffBump (X / 2) where
  rIn := X / 8
  rOut := X / 4
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

/-- A complex-valued Schwartz bump on the positive half of the band. -/
def positiveBandBump {X : ℝ} (hX : 0 < X) : 𝓢(ℝ, ℂ) :=
  (show HasCompactSupport
    (fun t : ℝ => (positiveBandBumpShape hX).normed volume t • (1 : ℂ)) from
      (ContDiffBump.hasCompactSupport_normed (positiveBandBumpShape hX)
        (μ := volume)).smul_right).toSchwartzMap
    ((ContDiffBump.contDiff_normed (positiveBandBumpShape hX)
      (μ := volume) (n := ⊤)).smul contDiff_const)

@[simp] theorem positiveBandBump_apply {X : ℝ} (hX : 0 < X) (t : ℝ) :
    positiveBandBump hX t =
      (positiveBandBumpShape hX).normed volume t • (1 : ℂ) := rfl

theorem integral_positiveBandBump {X : ℝ} (hX : 0 < X) :
    (∫ t : ℝ, positiveBandBump hX t) = (1 : ℂ) :=
  (positiveBandBumpShape hX).integral_normed_smul volume (1 : ℂ)

@[simp] theorem positiveBandBump_zero {X : ℝ} (hX : 0 < X) :
    positiveBandBump hX 0 = 0 := by
  have hd : (positiveBandBumpShape hX).rOut ≤ dist (0 : ℝ) (X / 2) := by
    change X / 4 ≤ dist (0 : ℝ) (X / 2)
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (by linarith : 0 < X / 2)]
    linarith
  rw [positiveBandBump_apply, ContDiffBump.normed_def,
    (positiveBandBumpShape hX).zero_of_le_dist hd, zero_div, zero_smul]

theorem support_positiveBandBump_subset {X : ℝ} (hX : 0 < X) :
    Function.support (positiveBandBump hX : ℝ → ℂ) ⊆ Set.Icc (-X) X := by
  intro t ht
  have hn : (positiveBandBumpShape hX).normed volume t ≠ 0 := by
    intro hz
    apply ht
    rw [positiveBandBump_apply, hz, zero_smul]
  have hb : t ∈ Metric.ball (X / 2) (X / 4) := by
    change t ∈ Metric.ball (X / 2) (positiveBandBumpShape hX).rOut
    rw [← (positiveBandBumpShape hX).support_normed_eq (μ := volume)]
    exact hn
  have habs : |t - X / 2| < X / 4 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hb
  obtain ⟨hlo, hhi⟩ := abs_lt.mp habs
  constructor <;> linarith

/-- Half the sum of the actual normalized bump and its reflection. -/
def normalizedBandBump {X : ℝ} (hX : 0 < X) : 𝓢(ℝ, ℂ) :=
  (1 / 2 : ℂ) • (positiveBandBump hX +
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (LinearIsometryEquiv.neg ℝ (E := ℝ)) (positiveBandBump hX))

@[simp] theorem normalizedBandBump_apply {X : ℝ} (hX : 0 < X) (t : ℝ) :
    normalizedBandBump hX t =
      (1 / 2 : ℂ) * (positiveBandBump hX t + positiveBandBump hX (-t)) := rfl

theorem normalizedBandBump_even {X : ℝ} (hX : 0 < X) :
    Function.Even (normalizedBandBump hX : ℝ → ℂ) := by
  intro t
  simp only [normalizedBandBump_apply, neg_neg, add_comm]

@[simp] theorem normalizedBandBump_zero {X : ℝ} (hX : 0 < X) :
    normalizedBandBump hX 0 = 0 := by
  simp only [normalizedBandBump_apply, neg_zero, positiveBandBump_zero, add_zero, mul_zero]

theorem support_normalizedBandBump_subset {X : ℝ} (hX : 0 < X) :
    Function.support (normalizedBandBump hX : ℝ → ℂ) ⊆ Set.Icc (-X) X := by
  apply Function.support_subset_iff'.mpr
  intro t ht
  have hnt : -t ∉ Set.Icc (-X) X := by
    intro h
    apply ht
    constructor <;> linarith [h.1, h.2]
  have hp := Function.support_subset_iff'.mp (support_positiveBandBump_subset hX)
  rw [normalizedBandBump_apply, hp t ht, hp (-t) hnt, add_zero, mul_zero]

theorem integral_normalizedBandBump {X : ℝ} (hX : 0 < X) :
    (∫ t : ℝ, normalizedBandBump hX t) = (1 : ℂ) := by
  let B : 𝓢(ℝ, ℂ) := positiveBandBump hX
  let R : 𝓢(ℝ, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := ℝ)) B
  have hR : (∫ t : ℝ, R t) = ∫ t : ℝ, B t := by
    exact integral_neg_eq_self (fun t : ℝ => B t) volume
  change (∫ t : ℝ, (1 / 2 : ℂ) • (B t + R t)) = 1
  rw [integral_smul, integral_add B.integrable R.integrable, hR]
  change (1 / 2 : ℂ) •
    ((∫ t : ℝ, positiveBandBump hX t) + ∫ t : ℝ, positiveBandBump hX t) = 1
  rw [integral_positiveBandBump hX]
  norm_num

/-- All properties of the concrete normalized bump required for the constant mode. -/
theorem normalizedBandBump_spec {X : ℝ} (hX : 0 < X) :
    Function.Even (normalizedBandBump hX : ℝ → ℂ) ∧
      normalizedBandBump hX 0 = 0 ∧
      Function.support (normalizedBandBump hX : ℝ → ℂ) ⊆ Set.Icc (-X) X ∧
      (∫ t : ℝ, normalizedBandBump hX t) = (1 : ℂ) :=
  ⟨normalizedBandBump_even hX, normalizedBandBump_zero hX,
    support_normalizedBandBump_subset hX, integral_normalizedBandBump hX⟩

theorem exists_even_normalizedBandBump {X : ℝ} (hX : 0 < X) :
    ∃ H : 𝓢(ℝ, ℂ), Function.Even (H : ℝ → ℂ) ∧ H 0 = 0 ∧
      Function.support (H : ℝ → ℂ) ⊆ Set.Icc (-X) X ∧
      (∫ t : ℝ, H t) = (1 : ℂ) :=
  ⟨normalizedBandBump hX, normalizedBandBump_spec hX⟩

#print axioms positiveBandBump
#print axioms integral_positiveBandBump
#print axioms normalizedBandBump_spec
#print axioms exists_even_normalizedBandBump

end MasulloLocal

/- Source module: MasulloLocal/SupportDrop.lean -/
/-!
# Fourier support under a dilation difference

This module works in the genuine real Schwartz space with Mathlib's Fourier transform.
It is an independent component of the proposed finite-bandwidth periodization sequence.
No periodization, quotient identification, or Riemann-hypothesis input is assumed.
-/

open scoped SchwartzMap FourierTransform
open MeasureTheory

set_option autoImplicit false

noncomputable section

namespace MasulloLocal

/-- The actual dilation `f(x) ↦ f(p*x)` as a continuous linear map on Schwartz space. -/
def dilation (p : ℝ) (hp : p ≠ 0) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ) (Units.mk0 p hp))

@[simp] theorem dilation_apply (p : ℝ) (hp : p ≠ 0) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    dilation p hp f x = f (p * x) := rfl

/-- The unnormalized Euler difference. -/
def eulerDifference (p : ℝ) (hp : p ≠ 0) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ) - dilation p hp

@[simp] theorem eulerDifference_apply (p : ℝ) (hp : p ≠ 0)
    (f : 𝓢(ℝ, ℂ)) (x : ℝ) : eulerDifference p hp f x = f x - f (p * x) := rfl

/-- Fourier support in the closed symmetric additive interval of radius `X`. -/
def InBand (X : ℝ) (f : 𝓢(ℝ, ℂ)) : Prop :=
  Function.support (⇑(𝓕 f : 𝓢(ℝ, ℂ))) ⊆ Set.Icc (-X) X

/-- Positive dilation in the Fourier transform, evaluated at `p*ξ`. -/
theorem fourier_dilation_mul {p : ℝ} (hp : 0 < p) (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (dilation p hp.ne' f) (p * ξ) = (p : ℂ)⁻¹ * 𝓕 f ξ := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  change (∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * (p * ξ)) * Complex.I) •
    f (p * x)) = (p : ℂ)⁻¹ * 𝓕 f ξ
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  have h := Measure.integral_comp_mul_left
    (fun y : ℝ => Complex.exp (↑(-2 * Real.pi * y * ξ) * Complex.I) • f y) p
  rw [abs_of_pos (inv_pos.mpr hp)] at h
  simpa only [Complex.real_smul, Complex.ofReal_inv, smul_eq_mul,
    mul_assoc, mul_left_comm, mul_comm] using h

/-- Positive dilation at an arbitrary Fourier argument. -/
theorem fourier_dilation {p : ℝ} (hp : 0 < p) (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (dilation p hp.ne' f) ξ = (p : ℂ)⁻¹ * 𝓕 f (ξ / p) := by
  have h := fourier_dilation_mul hp f (ξ / p)
  simpa only [mul_div_cancel₀ _ hp.ne'] using h

/-- The Fourier recurrence for the actual Euler difference. -/
theorem fourier_eulerDifference_mul {p : ℝ} (hp : 0 < p) (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (eulerDifference p hp.ne' f) (p * ξ) =
      𝓕 f (p * ξ) - (p : ℂ)⁻¹ * 𝓕 f ξ := by
  change ((FourierTransform.fourierCLM ℂ 𝓢(ℝ, ℂ))
    (f - dilation p hp.ne' f)) (p * ξ) = _
  rw [map_sub]
  change 𝓕 f (p * ξ) - 𝓕 (dilation p hp.ne' f) (p * ξ) = _
  rw [fourier_dilation_mul hp]

/-- A Schwartz function satisfying the dilation recurrence outside a band vanishes there.

The order-two Schwartz seminorm rules out the `1/x` tail that a nonzero solution
would have on the geometric sequence `p^n*x`.
-/
theorem support_subset_of_dilation_recurrence {p X : ℝ} (hp : 1 < p) (hX : 0 ≤ X)
    (f : 𝓢(ℝ, ℂ))
    (hf : ∀ ξ : ℝ, X < |ξ| → (p : ℂ) * f (p * ξ) = f ξ) :
    Function.support f ⊆ Set.Icc (-X) X := by
  apply Function.support_subset_iff'.2
  intro ξ hξ
  have hξabs : X < |ξ| := by
    by_contra h
    exact hξ (abs_le.mp (le_of_not_gt h))
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hξpos : 0 < |ξ| := lt_of_le_of_lt hX hξabs
  have hrec (n : ℕ) : p ^ n * ‖f (p ^ n * ξ)‖ = ‖f ξ‖ := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hout : X < |p ^ n * ξ| := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg hp0.le n)]
        exact lt_of_lt_of_le hξabs (le_mul_of_one_le_left (abs_nonneg ξ) (one_le_pow₀ hp.le))
      have hh := congrArg norm (hf (p ^ n * ξ) hout)
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0] at hh
      calc
        p ^ (n + 1) * ‖f (p ^ (n + 1) * ξ)‖
            = p ^ n * (p * ‖f (p * (p ^ n * ξ))‖) := by
              simp only [pow_succ, mul_assoc, mul_left_comm, mul_comm]
        _ = p ^ n * ‖f (p ^ n * ξ)‖ := by rw [hh]
        _ = ‖f ξ‖ := ih
  have hbound (n : ℕ) :
      p ^ n * (|ξ| ^ 2 * ‖f ξ‖) ≤ SchwartzMap.seminorm ℂ 2 0 f := by
    calc
      p ^ n * (|ξ| ^ 2 * ‖f ξ‖)
          = ‖p ^ n * ξ‖ ^ 2 * ‖f (p ^ n * ξ)‖ := by
              rw [← hrec n, Real.norm_eq_abs, abs_mul,
                abs_of_nonneg (pow_nonneg hp0.le n)]
              ring
      _ ≤ SchwartzMap.seminorm ℂ 2 0 f := f.norm_pow_mul_le_seminorm ℂ 2 _
  by_contra hne
  have hpos : 0 < |ξ| ^ 2 * ‖f ξ‖ := mul_pos (pow_pos hξpos 2) (norm_pos_iff.mpr hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
    (SchwartzMap.seminorm ℂ 2 0 f / (|ξ| ^ 2 * ‖f ξ‖)) hp
  exact (not_lt_of_ge (hbound n)) ((div_lt_iff₀ hpos).mp hn)

/-- Dividing a genuine Schwartz dilation difference loses exactly the dilation factor
in its additive Fourier bandwidth. The proof uses rapid decay, not a division theorem
or an assumed support property of the unknown function. -/
theorem inBand_of_eulerDifference {p X : ℝ} (hp : 1 < p) (hX : 0 ≤ X)
    (h : 𝓢(ℝ, ℂ)) (hband : InBand (p * X) (eulerDifference p (ne_of_gt (lt_trans zero_lt_one hp)) h)) :
    InBand X h := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  apply support_subset_of_dilation_recurrence hp hX (𝓕 h)
  intro ξ hξ
  have hzero : 𝓕 (eulerDifference p hp0.ne' h) (p * ξ) = 0 := by
    apply (Function.support_subset_iff'.mp hband)
    intro hmem
    have hh := abs_le.mpr hmem
    rw [abs_mul, abs_of_pos hp0] at hh
    nlinarith
  have hvalue : 𝓕 (eulerDifference p hp0.ne' h) (p * ξ) =
      𝓕 h (p * ξ) - (p : ℂ)⁻¹ * 𝓕 h ξ := by
    exact fourier_eulerDifference_mul hp0 h ξ
  have hstep : 𝓕 h (p * ξ) = (p : ℂ)⁻¹ * 𝓕 h ξ :=
    sub_eq_zero.mp (hvalue.symm.trans hzero)
  rw [hstep, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hp0.ne'), one_mul]

#print axioms fourier_dilation_mul
#print axioms support_subset_of_dilation_recurrence
#print axioms inBand_of_eulerDifference

end MasulloLocal

/- Source module: MasulloLocal/BandSpace.lean -/
/-!
# The actual even two-residue Paley–Wiener core

`E X` is a subspace of Mathlib's Schwartz space, with its inherited topology.
The two residues are the value at the additive origin and the Fourier value at
the additive origin. No quotient or periodization properties are built into it.
-/

open scoped SchwartzMap FourierTransform
open MeasureTheory

set_option autoImplicit false

noncomputable section

namespace MasulloLocal

theorem inBand_zero (X : ℝ) : InBand X (0 : 𝓢(ℝ, ℂ)) := by
  intro ξ hξ
  exact False.elim (hξ (by simp))

theorem InBand.add {X : ℝ} {f g : 𝓢(ℝ, ℂ)} (hf : InBand X f) (hg : InBand X g) :
    InBand X (f + g) := by
  apply Function.support_subset_iff'.2
  intro ξ hξ
  rw [FourierTransform.fourier_add]
  change 𝓕 f ξ + 𝓕 g ξ = 0
  rw [(Function.support_subset_iff'.mp hf) ξ hξ,
    (Function.support_subset_iff'.mp hg) ξ hξ, add_zero]

theorem InBand.smul {X : ℝ} {f : 𝓢(ℝ, ℂ)} (hf : InBand X f) (c : ℂ) :
    InBand X (c • f) := by
  apply Function.support_subset_iff'.2
  intro ξ hξ
  rw [FourierTransform.fourier_smul]
  change c • 𝓕 f ξ = 0
  rw [(Function.support_subset_iff'.mp hf) ξ hξ, smul_zero]

/-- Even Schwartz functions with both additive residues zero and Fourier radius `X`. -/
def E (X : ℝ) : Submodule ℂ 𝓢(ℝ, ℂ) where
  carrier := {f | Function.Even (f : ℝ → ℂ) ∧ f 0 = 0 ∧ 𝓕 f 0 = 0 ∧ InBand X f}
  zero_mem' := by
    refine ⟨fun _ => rfl, rfl, ?_, inBand_zero X⟩
    simp
  add_mem' := by
    rintro f g ⟨hf, hf0, hFf0, hfB⟩ ⟨hg, hg0, hFg0, hgB⟩
    refine ⟨?_, ?_, ?_, hfB.add hgB⟩
    · intro x
      change f (-x) + g (-x) = f x + g x
      rw [hf x, hg x]
    · change f 0 + g 0 = 0
      rw [hf0, hg0, add_zero]
    · rw [FourierTransform.fourier_add]
      change 𝓕 f 0 + 𝓕 g 0 = 0
      rw [hFf0, hFg0, add_zero]
  smul_mem' := by
    rintro c f ⟨hf, hf0, hFf0, hfB⟩
    refine ⟨?_, ?_, ?_, hfB.smul c⟩
    · intro x
      change c • f (-x) = c • f x
      rw [hf x]
    · change c • f 0 = 0
      rw [hf0, smul_zero]
    · rw [FourierTransform.fourier_smul]
      change c • 𝓕 f 0 = 0
      rw [hFf0, smul_zero]

@[simp] theorem mem_E {X : ℝ} {f : 𝓢(ℝ, ℂ)} :
    f ∈ E X ↔ Function.Even (f : ℝ → ℂ) ∧ f 0 = 0 ∧ 𝓕 f 0 = 0 ∧ InBand X f := Iff.rfl

/-- The Fourier residue is literally the additive integral. -/
theorem fourier_zero_eq_integral (f : 𝓢(ℝ, ℂ)) : 𝓕 f 0 = ∫ x : ℝ, f x := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  simp

/-- Monotonicity of the additive Fourier band. -/
theorem InBand.mono {X Y : ℝ} {f : 𝓢(ℝ, ℂ)} (hf : InBand X f) (hXY : X ≤ Y) :
    InBand Y f := by
  intro ξ hξ
  obtain ⟨hlo, hhi⟩ := hf hξ
  exact ⟨(neg_le_neg hXY).trans hlo, hhi.trans hXY⟩

/-- Dilation multiplies the Fourier radius by `p`. -/
theorem InBand.dilation {p X : ℝ} (hp : 0 < p) {f : 𝓢(ℝ, ℂ)} (hf : InBand X f) :
    InBand (p * X) (dilation p hp.ne' f) := by
  apply Function.support_subset_iff'.2
  intro ξ hξ
  rw [fourier_dilation hp]
  have hout : ξ / p ∉ Set.Icc (-X) X := by
    intro hmem
    apply hξ
    constructor
    · have h := (le_div_iff₀ hp).mp hmem.1
      nlinarith
    · have h := (div_le_iff₀ hp).mp hmem.2
      nlinarith
  rw [(Function.support_subset_iff'.mp hf) (ξ / p) hout, mul_zero]

/-- The Euler difference has the prescribed target band and preserves both residues. -/
theorem eulerDifference_mem_E {p X : ℝ} (hp : 1 < p) (hX : 0 ≤ X)
    {f : 𝓢(ℝ, ℂ)} (hf : f ∈ E X) :
    eulerDifference p (ne_of_gt (lt_trans zero_lt_one hp)) f ∈ E (p * X) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  obtain ⟨hfe, hf0, hFf0, hfB⟩ := hf
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    simp only [eulerDifference_apply, mul_neg, hfe x, hfe (p * x)]
  · simp [hf0]
  · have h := fourier_eulerDifference_mul hp0 f 0
    simpa only [mul_zero, hFf0, sub_zero] using h
  · have hfx : InBand (p * X) f := hfB.mono (by nlinarith)
    have hdx : InBand (p * X) (dilation p hp0.ne' f) := hfB.dilation hp0
    change InBand (p * X) (f - dilation p hp0.ne' f)
    simpa only [neg_one_smul, sub_eq_add_neg] using hfx.add (hdx.smul (-1))

/-- The first arrow in the proposed exact sequence, with the actual inherited topologies. -/
def eulerBandMap {p X : ℝ} (hp : 1 < p) (hX : 0 ≤ X) : E X →L[ℂ] E (p * X) :=
  ((eulerDifference p (ne_of_gt (lt_trans zero_lt_one hp))).comp (E X).subtypeL).codRestrict
    (E (p * X)) (fun f => eulerDifference_mem_E hp hX f.property)

@[simp] theorem eulerBandMap_apply {p X : ℝ} (hp : 1 < p) (hX : 0 ≤ X)
    (f : E X) (x : ℝ) :
    (eulerBandMap hp hX f : 𝓢(ℝ, ℂ)) x = (f : 𝓢(ℝ, ℂ)) x - (f : 𝓢(ℝ, ℂ)) (p * x) := rfl

/-- A Schwartz function cannot be invariant under an expanding dilation. -/
theorem eulerDifference_eq_zero_iff {p : ℝ} (hp : 1 < p) (f : 𝓢(ℝ, ℂ)) :
    eulerDifference p (ne_of_gt (lt_trans zero_lt_one hp)) f = 0 ↔ f = 0 := by
  constructor
  · intro heq
    have hp0 : 0 < p := lt_trans zero_lt_one hp
    have hb : InBand 0 f := inBand_of_eulerDifference hp (le_refl 0) f (by
      rw [heq]
      exact inBand_zero (p * 0))
    have hF0 : 𝓕 f 0 = 0 := by
      have hd : 𝓕 f 0 - (p : ℂ)⁻¹ * 𝓕 f 0 = 0 := by
        calc
          𝓕 f 0 - (p : ℂ)⁻¹ * 𝓕 f 0
              = 𝓕 (eulerDifference p hp0.ne' f) (p * 0) := by
                  simpa only [mul_zero] using (fourier_eulerDifference_mul hp0 f 0).symm
          _ = 0 := by simp [heq]
      by_contra hne
      have hc : (1 : ℂ) = (p : ℂ)⁻¹ :=
        mul_right_cancel₀ hne (by simpa only [one_mul] using sub_eq_zero.mp hd)
      have hp1 : (p : ℂ) = 1 := inv_eq_one.mp hc.symm
      have hp1r : p = 1 := by exact_mod_cast hp1
      exact (ne_of_gt hp) hp1r
    apply (FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ)).injective
    change 𝓕 f = 𝓕 (0 : 𝓢(ℝ, ℂ))
    rw [FourierTransform.fourier_zero]
    ext ξ
    by_cases hξ : ξ = 0
    · simpa [hξ] using hF0
    · apply (Function.support_subset_iff'.mp hb)
      intro hmem
      exact hξ (le_antisymm hmem.2 (by simpa only [neg_zero] using hmem.1))
  · rintro rfl
    exact map_zero _

theorem eulerDifference_injective {p : ℝ} (hp : 1 < p) :
    Function.Injective (eulerDifference p (ne_of_gt (lt_trans zero_lt_one hp))) := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply (eulerDifference_eq_zero_iff hp (f - g)).mp
  rw [map_sub, hfg, sub_self]

/-- Injectivity of the first arrow of the finite-bandwidth sequence. -/
theorem eulerBandMap_injective {p X : ℝ} (hp : 1 < p) (hX : 0 ≤ X) :
    Function.Injective (eulerBandMap hp hX) := by
  intro f g hfg
  apply Subtype.ext
  apply eulerDifference_injective hp
  exact congrArg (fun y : E (p * X) => (y : 𝓢(ℝ, ℂ))) hfg

#print axioms eulerDifference_mem_E
#print axioms eulerBandMap
#print axioms eulerBandMap_injective

end MasulloLocal

/- Source module: MasulloLocal/OrbitSums.lean -/
/-!
# Actual multiplicative periodization on the real Schwartz core

The series is the bilateral sum of `f(p^n * exp x)`. Its convergence is proved
from Schwartz decay at infinity and a first-derivative bound at the origin.
Evenness and the Fourier residue condition are unnecessary for this convergence.
-/

open scoped SchwartzMap FourierTransform
open MeasureTheory Filter Topology

set_option autoImplicit false

noncomputable section

namespace MasulloLocal

/-- A global first-order bound at the additive origin, from a Schwartz seminorm. -/
theorem norm_sub_zero_le_seminorm (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖f x - f 0‖ ≤ SchwartzMap.seminorm ℂ 0 1 f * ‖x‖ := by
  have hder (y : ℝ) (_hy : y ∈ (Set.univ : Set ℝ)) :
      ‖fderiv ℝ f y‖ ≤ SchwartzMap.seminorm ℂ 0 1 f := by
    rw [← norm_iteratedFDeriv_one]
    exact f.norm_iteratedFDeriv_le_seminorm ℂ 1 y
  simpa only [sub_zero] using
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => f.differentiable y) hder (Set.mem_univ 0) (Set.mem_univ x)

/-- The positive dilation orbit of a Schwartz function is absolutely summable. -/
theorem summable_nat_orbit {p t : ℝ} (hp : 1 < p) (ht : 0 < t) (f : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℕ => f (p ^ n * t)) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hgeom := summable_geometric_of_lt_one (inv_nonneg.mpr hp0.le)
    (inv_lt_one_of_one_lt₀ hp)
  apply (hgeom.mul_left (SchwartzMap.seminorm ℂ 1 0 f / t)).of_norm_bounded
  intro n
  have hy : 0 < p ^ n * t := mul_pos (pow_pos hp0 n) ht
  have hdecay := f.norm_pow_mul_le_seminorm ℂ 1 (p ^ n * t)
  rw [pow_one, Real.norm_eq_abs, abs_of_pos hy] at hdecay
  calc
    ‖f (p ^ n * t)‖ ≤ SchwartzMap.seminorm ℂ 1 0 f / (p ^ n * t) :=
      (le_div_iff₀ hy).mpr (by simpa only [mul_comm] using hdecay)
    _ = SchwartzMap.seminorm ℂ 1 0 f / t * (p⁻¹) ^ n := by
      rw [inv_pow]
      field_simp

/-- After removing the value at the origin, a contracting orbit is absolutely summable. -/
theorem summable_nat_contract_sub_zero {p t : ℝ} (hp : 1 < p) (ht : 0 < t)
    (f : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℕ => f ((p⁻¹) ^ n * t) - f 0) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hgeom := summable_geometric_of_lt_one (inv_nonneg.mpr hp0.le)
    (inv_lt_one_of_one_lt₀ hp)
  apply (hgeom.mul_left (SchwartzMap.seminorm ℂ 0 1 f * t)).of_norm_bounded
  intro n
  have hy : 0 < (p⁻¹) ^ n * t := mul_pos (pow_pos (inv_pos.mpr hp0) n) ht
  have h := norm_sub_zero_le_seminorm f ((p⁻¹) ^ n * t)
  rw [Real.norm_eq_abs, abs_of_pos hy] at h
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

/-- Absolute convergence of the actual bilateral orbit sum. -/
theorem summable_int_orbit {p t : ℝ} (hp : 1 < p) (ht : 0 < t)
    (f : 𝓢(ℝ, ℂ)) (hf0 : f 0 = 0) :
    Summable (fun n : ℤ => f (p ^ n * t)) := by
  apply Summable.of_nat_of_neg_add_one
  · simpa only [zpow_natCast] using summable_nat_orbit hp ht f
  · have h := (summable_nat_contract_sub_zero hp ht f).comp_injective Nat.succ_injective
    simpa only [Function.comp_def, Nat.succ_eq_add_one, hf0, sub_zero, zpow_neg,
      ← Int.natCast_add_one, zpow_natCast, inv_pow] using h

/-- Periodization in logarithmic coordinates. -/
def periodization (p : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  ∑' n : ℤ, f (p ^ n * Real.exp x)

theorem periodization_summable {p : ℝ} (hp : 1 < p) (f : 𝓢(ℝ, ℂ))
    (hf0 : f 0 = 0) (x : ℝ) :
    Summable (fun n : ℤ => f (p ^ n * Real.exp x)) :=
  summable_int_orbit hp (Real.exp_pos x) f hf0

/-- The period is exactly `log p`, using reindexing of the actual bilateral series. -/
theorem periodization_periodic {p : ℝ} (hp : 1 < p) (f : 𝓢(ℝ, ℂ)) :
    Function.Periodic (periodization p f) (Real.log p) := by
  intro x
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  change (∑' n : ℤ, f (p ^ n * Real.exp (x + Real.log p))) =
    ∑' n : ℤ, f (p ^ n * Real.exp x)
  calc
    (∑' n : ℤ, f (p ^ n * Real.exp (x + Real.log p)))
        = ∑' n : ℤ, f (p ^ (n + 1) * Real.exp x) := by
            congr 1
            funext n
            rw [Real.exp_add, Real.exp_log hp0, zpow_add₀ hp0.ne', zpow_one]
            congr 1
            ring
    _ = ∑' n : ℤ, f (p ^ n * Real.exp x) :=
      (Equiv.addRight (1 : ℤ)).tsum_eq (fun n => f (p ^ n * Real.exp x))

/-- The expanding half of the Euler-difference orbit telescopes to the initial value. -/
theorem tsum_nat_orbit_eulerDifference {p t : ℝ} (hp : 1 < p) (ht : 0 < t)
    (g : 𝓢(ℝ, ℂ)) :
    (∑' n : ℕ, eulerDifference p (ne_of_gt (lt_trans zero_lt_one hp)) g (p ^ n * t)) =
      g t := by
  have hs := summable_nat_orbit hp ht g
  have hs' := hs.comp_injective Nat.succ_injective
  calc
    (∑' n : ℕ, eulerDifference p (ne_of_gt (lt_trans zero_lt_one hp)) g (p ^ n * t))
        = ∑' n : ℕ, (g (p ^ n * t) - g (p ^ (n + 1) * t)) := by
            congr 1
            funext n
            simp only [eulerDifference_apply, pow_succ, mul_left_comm, mul_comm]
    _ = (∑' n : ℕ, g (p ^ n * t)) - ∑' n : ℕ, g (p ^ (n + 1) * t) :=
      hs.tsum_sub hs'
    _ = g t := by
      rw [hs.tsum_eq_zero_add]
      simp only [pow_zero, one_mul, add_sub_cancel_right]

/-- The contracting half retains the genuine value at the additive origin. -/
theorem tsum_nat_contract_eulerDifference {p t : ℝ} (hp : 1 < p) (ht : 0 < t)
    (g : 𝓢(ℝ, ℂ)) :
    (∑' n : ℕ, eulerDifference p (ne_of_gt (lt_trans zero_lt_one hp)) g
      (p ^ (-((n : ℤ) + 1)) * t)) = g 0 - g t := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  let a : ℕ → ℂ := fun n => g ((p⁻¹) ^ n * t) - g 0
  have hs : Summable a := summable_nat_contract_sub_zero hp ht g
  have hs' := hs.comp_injective Nat.succ_injective
  calc
    (∑' n : ℕ, eulerDifference p hp0.ne' g (p ^ (-((n : ℤ) + 1)) * t))
        = ∑' n : ℕ, (a (n + 1) - a n) := by
            congr 1
            funext n
            have hm : p * ((p⁻¹) ^ (n + 1) * t) = (p⁻¹) ^ n * t := by
              calc
                p * ((p⁻¹) ^ (n + 1) * t)
                    = (p * p⁻¹) * ((p⁻¹) ^ n * t) := by rw [pow_succ']; ring
                _ = (p⁻¹) ^ n * t := by rw [mul_inv_cancel₀ hp0.ne', one_mul]
            simp only [eulerDifference_apply, zpow_neg, ← Int.natCast_add_one,
              zpow_natCast, ← inv_pow]
            rw [hm]
            dsimp [a]
            ring
    _ = (∑' n : ℕ, a (n + 1)) - ∑' n : ℕ, a n := hs'.tsum_sub hs
    _ = g 0 - g t := by
      rw [hs.tsum_eq_zero_add]
      simp only [a, pow_zero, one_mul]
      ring

#print axioms summable_int_orbit
#print axioms periodization_periodic
#print axioms tsum_nat_orbit_eulerDifference
#print axioms tsum_nat_contract_eulerDifference

end MasulloLocal

/- Source module: MasulloLocal/Periodization.lean -/
open scoped SchwartzMap FourierTransform
open MeasureTheory Filter Topology
set_option autoImplicit false
noncomputable section
namespace MasulloLocal

/-- The complete bilateral Euler-difference orbit sums to `g(0)`.

Both halves are absolutely convergent. Thus the retained origin value is not a
choice of conditional summation or a silently dropped endpoint.
-/
theorem tsum_int_orbit_eulerDifference {p t : ℝ} (hp : 1 < p) (ht : 0 < t)
    (g : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, eulerDifference p (ne_of_gt (lt_trans zero_lt_one hp)) g (p ^ n * t)) =
      g 0 := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  let δ : 𝓢(ℝ, ℂ) := eulerDifference p hp0.ne' g
  have hδ0 : δ 0 = 0 := by
    change g 0 - g (p * 0) = 0
    simp only [mul_zero, sub_self]
  have hspos : Summable (fun n : ℕ => eulerDifference p hp0.ne' g (p ^ (n : ℤ) * t)) :=
    by simpa only [zpow_natCast] using summable_nat_orbit hp ht δ
  have hsneg : Summable (fun n : ℕ =>
      eulerDifference p hp0.ne' g (p ^ (-((n : ℤ) + 1)) * t)) := by
    have h := (summable_nat_contract_sub_zero hp ht δ).comp_injective Nat.succ_injective
    simpa only [Function.comp_def, Nat.succ_eq_add_one, hδ0, sub_zero, zpow_neg,
      ← Int.natCast_add_one, zpow_natCast, inv_pow] using h
  rw [tsum_of_nat_of_neg_add_one
    (f := fun n : ℤ => eulerDifference p hp0.ne' g (p ^ n * t)) hspos hsneg]
  simp only [zpow_natCast]
  rw [tsum_nat_orbit_eulerDifference hp ht g, tsum_nat_contract_eulerDifference hp ht g]
  ring

/-- The constant boundary term in logarithmic coordinates. -/
theorem periodization_eulerDifference {p : ℝ} (hp : 1 < p) (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    periodization p (eulerDifference p (ne_of_gt (lt_trans zero_lt_one hp)) g) x = g 0 :=
  tsum_int_orbit_eulerDifference hp (Real.exp_pos x) g

/-- The first arrow lands in the kernel of the actual, convergent periodization. -/
theorem periodization_eulerBandMap {p X : ℝ} (hp : 1 < p) (hX : 0 ≤ X)
    (f : E X) (x : ℝ) :
    periodization p (eulerBandMap hp hX f : 𝓢(ℝ, ℂ)) x = 0 := by
  change periodization p (eulerDifference p (ne_of_gt (lt_trans zero_lt_one hp))
    (f : 𝓢(ℝ, ℂ))) x = 0
  rw [periodization_eulerDifference hp]
  exact f.property.2.1

#print axioms summable_int_orbit
#print axioms periodization_periodic
#print axioms periodization_eulerDifference
#print axioms periodization_eulerBandMap

end MasulloLocal

/- Source module: MasulloLocal/ConstantMode.lean -/
/-!
# A constant circle mode from an actual Fourier-side bump

If `H` is even, vanishes at zero, and is supported in `[-X,X]`, the Euler
difference of its inverse Fourier transform lies in the actual two-residue
space `E (p * X)`. Its periodization is the constant `∫ H`. In particular,
normalizing this integral to one gives the constant circle mode.

The inverse Fourier transform itself is deliberately not asserted to belong
to `E X`: under the normalization its value at the origin is one.
-/

open scoped SchwartzMap FourierTransform
open MeasureTheory

set_option autoImplicit false

noncomputable section

namespace MasulloLocal

/-- The inverse Fourier value at the additive origin is the ordinary integral. -/
theorem fourierInv_zero_eq_integral (H : 𝓢(ℝ, ℂ)) :
    𝓕⁻ H 0 = ∫ x : ℝ, H x := by
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_zero]
  simpa only [SchwartzMap.fourier_coe] using fourier_zero_eq_integral H

/-- Reflection commutes with inverse Fourier transformation. -/
theorem even_fourierInv (H : 𝓢(ℝ, ℂ))
    (hHe : Function.Even (H : ℝ → ℂ)) :
    Function.Even (⇑(𝓕⁻ H : 𝓢(ℝ, ℂ))) := by
  intro t
  have hcomp :
      (H : ℝ → ℂ) ∘ (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) =
      (H : ℝ → ℂ) := by
    funext x
    exact hHe x
  have h := Real.fourierInv_comp_linearIsometry
    (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) (H : ℝ → ℂ) t
  rw [hcomp] at h
  change (𝓕⁻ (H : ℝ → ℂ)) t = (𝓕⁻ (H : ℝ → ℂ)) (-t) at h
  simpa only [SchwartzMap.fourierInv_coe] using h.symm

/-- The Euler difference cancels the origin value even when that value is nonzero. -/
theorem eulerDifference_mem_E_of_even_fourier_zero
    {p X : ℝ} (hp : 1 < p) (hX : 0 ≤ X)
    (g : 𝓢(ℝ, ℂ)) (hge : Function.Even (g : ℝ → ℂ))
    (hgF0 : 𝓕 g 0 = 0) (hgB : InBand X g) :
    eulerDifference p (ne_of_gt (lt_trans zero_lt_one hp)) g ∈ E (p * X) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    simp only [eulerDifference_apply, mul_neg, hge x, hge (p * x)]
  · simp only [eulerDifference_apply, mul_zero, sub_self]
  · have h := fourier_eulerDifference_mul hp0 g 0
    simpa only [mul_zero, hgF0, sub_zero] using h
  · have hgb' : InBand (p * X) g := hgB.mono (by nlinarith)
    have hdB : InBand (p * X) (dilation p hp0.ne' g) := hgB.dilation hp0
    change InBand (p * X) (g - dilation p hp0.ne' g)
    simpa only [neg_one_smul, sub_eq_add_neg] using hgb'.add (hdB.smul (-1))

/-- An explicit lift of the constant `∫ H`, before choosing its normalization. -/
def constantModeFromFourier {p X : ℝ} (hp : 1 < p) (hX : 0 < X)
    (H : 𝓢(ℝ, ℂ)) (hHe : Function.Even (H : ℝ → ℂ))
    (hH0 : H 0 = 0)
    (hHs : Function.support (H : ℝ → ℂ) ⊆ Set.Icc (-X) X) :
    E (p * X) :=
  ⟨eulerDifference p (ne_of_gt (lt_trans zero_lt_one hp)) (𝓕⁻ H),
    eulerDifference_mem_E_of_even_fourier_zero hp hX.le (𝓕⁻ H)
      (even_fourierInv H hHe)
      (by simpa only [FourierTransform.fourier_fourierInv_eq] using hH0)
      (by simpa only [InBand, FourierTransform.fourier_fourierInv_eq] using hHs)⟩

@[simp] theorem constantModeFromFourier_apply {p X : ℝ} (hp : 1 < p) (hX : 0 < X)
    (H : 𝓢(ℝ, ℂ)) (hHe : Function.Even (H : ℝ → ℂ))
    (hH0 : H 0 = 0)
    (hHs : Function.support (H : ℝ → ℂ) ⊆ Set.Icc (-X) X) (t : ℝ) :
    (constantModeFromFourier hp hX H hHe hH0 hHs : 𝓢(ℝ, ℂ)) t =
      𝓕⁻ H t - 𝓕⁻ H (p * t) := rfl

/-- The complete, absolutely convergent periodization retains the normalized
origin value of the inverse Fourier transform. -/
theorem periodization_constantModeFromFourier
    {p X : ℝ} (hp : 1 < p) (hX : 0 < X)
    (H : 𝓢(ℝ, ℂ)) (hHe : Function.Even (H : ℝ → ℂ))
    (hH0 : H 0 = 0)
    (hHs : Function.support (H : ℝ → ℂ) ⊆ Set.Icc (-X) X) (x : ℝ) :
    periodization p (constantModeFromFourier hp hX H hHe hH0 hHs : 𝓢(ℝ, ℂ)) x =
      ∫ t : ℝ, H t := by
  change periodization p
    (eulerDifference p (ne_of_gt (lt_trans zero_lt_one hp)) (𝓕⁻ H)) x = _
  rw [periodization_eulerDifference hp, fourierInv_zero_eq_integral]

/-- A normalized even Fourier-side bump supplies the actual constant circle mode. -/
theorem exists_constantMode_of_normalizedBandBump
    {p X : ℝ} (hp : 1 < p) (hX : 0 < X)
    (H : 𝓢(ℝ, ℂ)) (hHe : Function.Even (H : ℝ → ℂ))
    (hH0 : H 0 = 0)
    (hHs : Function.support (H : ℝ → ℂ) ⊆ Set.Icc (-X) X)
    (hHI : (∫ t : ℝ, H t) = 1) :
    ∃ f : E (p * X), ∀ x : ℝ, periodization p (f : 𝓢(ℝ, ℂ)) x = 1 := by
  refine ⟨constantModeFromFourier hp hX H hHe hH0 hHs, ?_⟩
  intro x
  rw [periodization_constantModeFromFourier hp hX H hHe hH0 hHs x, hHI]

#print axioms fourierInv_zero_eq_integral
#print axioms even_fourierInv
#print axioms eulerDifference_mem_E_of_even_fourier_zero
#print axioms constantModeFromFourier
#print axioms periodization_constantModeFromFourier
#print axioms exists_constantMode_of_normalizedBandBump

end MasulloLocal

/- Source module: MasulloLocal/BandNontrivial.lean -/
open scoped SchwartzMap FourierTransform

set_option autoImplicit false

noncomputable section

namespace MasulloLocal

/-- With both residues imposed, a nonpositive Fourier band contains only zero. -/
theorem eq_zero_of_mem_E_nonpos {X : ℝ} (hX : X ≤ 0) {f : 𝓢(ℝ, ℂ)}
    (hf : f ∈ E X) : f = 0 := by
  have hF0 : 𝓕 f 0 = 0 := hf.2.2.1
  have hB : InBand X f := hf.2.2.2
  apply (FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ)).injective
  change 𝓕 f = 𝓕 (0 : 𝓢(ℝ, ℂ))
  rw [FourierTransform.fourier_zero]
  ext ξ
  by_cases hξ : ξ = 0
  · simpa [hξ] using hF0
  · by_contra hne
    have hmem : ξ ∈ Set.Icc (-X) X := hB hne
    have : ξ = 0 := by
      rcases hmem with ⟨hlo, hhi⟩
      linarith
    exact hξ this

/-- A constant-one orbit sum forces strictly positive bandwidth. -/
theorem pos_band_of_periodization_one {p X : ℝ} (hp : 1 < p)
    (f : E (p * X)) (hf : ∀ x : ℝ, periodization p (f : 𝓢(ℝ, ℂ)) x = 1) :
    0 < X := by
  by_contra hX
  have hX' : X ≤ 0 := le_of_not_gt hX
  have hpx : p * X ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
    (le_of_lt (lt_trans zero_lt_one hp)) hX'
  have hz : (f : 𝓢(ℝ, ℂ)) = 0 := eq_zero_of_mem_E_nonpos hpx f.property
  have h := hf 0
  simp [hz, periodization] at h

#print axioms eq_zero_of_mem_E_nonpos
#print axioms pos_band_of_periodization_one

end MasulloLocal

/- Source module: MasulloLocal/ConstantSection.lean -/
open scoped SchwartzMap FourierTransform
set_option autoImplicit false
noncomputable section

namespace MasulloLocal

/-- Every positive Fourier band admits an actual constant-one orbit sum. -/
theorem exists_constantMode {p X : ℝ} (hp : 1 < p) (hX : 0 < X) :
    ∃ f : E (p * X), ∀ x : ℝ, periodization p (f : 𝓢(ℝ, ℂ)) x = 1 := by
  obtain ⟨H, hHe, hH0, hHs, hHI⟩ := exists_even_normalizedBandBump hX
  exact exists_constantMode_of_normalizedBandBump hp hX H hHe hH0 hHs hHI

/-- The positivity condition on bandwidth is sharp. -/
theorem exists_constantMode_iff_pos {p X : ℝ} (hp : 1 < p) :
    (∃ f : E (p * X), ∀ x : ℝ, periodization p (f : 𝓢(ℝ, ℂ)) x = 1) ↔ 0 < X := by
  constructor
  · rintro ⟨f, hf⟩
    exact pos_band_of_periodization_one hp f hf
  · exact exists_constantMode hp

/-- A chosen lift of the constant function one, in the actual inherited band space. -/
def constantModeWitness {p X : ℝ} (hp : 1 < p) (hX : 0 < X) : E (p * X) :=
  Classical.choose (exists_constantMode hp hX)

theorem constantModeWitness_spec {p X : ℝ} (hp : 1 < p) (hX : 0 < X) (x : ℝ) :
    periodization p (constantModeWitness hp hX : 𝓢(ℝ, ℂ)) x = 1 :=
  Classical.choose_spec (exists_constantMode hp hX) x

/-- The retained constant direction admits a continuous complex-linear section. -/
def constantSection {p X : ℝ} (hp : 1 < p) (hX : 0 < X) : ℂ →L[ℂ] 𝓢(ℝ, ℂ) :=
  (E (p * X)).subtypeL.comp (ContinuousLinearMap.toSpanSingleton ℂ (constantModeWitness hp hX))

@[simp] theorem constantSection_apply {p X : ℝ} (hp : 1 < p) (hX : 0 < X) (c : ℂ) :
    constantSection hp hX c = c • (constantModeWitness hp hX : 𝓢(ℝ, ℂ)) := rfl

theorem constantSection_mem_E {p X : ℝ} (hp : 1 < p) (hX : 0 < X) (c : ℂ) :
    constantSection hp hX c ∈ E (p * X) :=
  (E (p * X)).smul_mem c (constantModeWitness hp hX).property

theorem periodization_constantSection {p X : ℝ} (hp : 1 < p) (hX : 0 < X)
    (c : ℂ) (x : ℝ) : periodization p (constantSection hp hX c) x = c := by
  let f : E (p * X) := constantModeWitness hp hX
  change (∑' n : ℤ, c • (f : 𝓢(ℝ, ℂ)) (p ^ n * Real.exp x)) = c
  rw [Summable.tsum_const_smul c (periodization_summable hp
    (f : 𝓢(ℝ, ℂ)) f.property.2.1 x)]
  change c • periodization p (constantModeWitness hp hX : 𝓢(ℝ, ℂ)) x = c
  rw [constantModeWitness_spec]
  exact smul_eq_mul c 1 |>.trans (mul_one c)

/-- An actual continuous linear lift of all constants exists exactly in positive bandwidth. -/
theorem constant_section_iff_pos {p X : ℝ} (hp : 1 < p) :
    (∃ S : ℂ →L[ℂ] 𝓢(ℝ, ℂ), ∀ c : ℂ,
      S c ∈ E (p * X) ∧ ∀ x : ℝ, periodization p (S c) x = c) ↔ 0 < X := by
  constructor
  · rintro ⟨S, hS⟩
    exact pos_band_of_periodization_one hp ⟨S 1, (hS 1).1⟩ (hS 1).2
  · intro hX
    exact ⟨constantSection hp hX, fun c =>
      ⟨constantSection_mem_E hp hX c, periodization_constantSection hp hX c⟩⟩

#print axioms exists_constantMode
#print axioms exists_constantMode_iff_pos
#print axioms constantSection
#print axioms constant_section_iff_pos

end MasulloLocal

/- Source module: Publication/ConstantSectionSolution.lean -/
open scoped SchwartzMap FourierTransform
set_option autoImplicit false
noncomputable section

/-- The exact public statement uses only upstream Mathlib objects. -/
theorem constantSectionSolution :
    ∀ (p X : ℝ), 1 < p →
      ((∃ S : ℂ →L[ℂ] 𝓢(ℝ, ℂ), ∀ c : ℂ,
        Function.Even (S c : ℝ → ℂ) ∧
        S c 0 = 0 ∧ 𝓕 (S c) 0 = 0 ∧
        Function.support (⇑(𝓕 (S c) : 𝓢(ℝ, ℂ))) ⊆ Set.Icc (-(p * X)) (p * X) ∧
        ∀ x : ℝ, (∑' n : ℤ, (S c) (p ^ n * Real.exp x)) = c) ↔ 0 < X) := by
  intro p X hp
  simpa only [MasulloLocal.mem_E, MasulloLocal.InBand, MasulloLocal.periodization, and_assoc]
    using (MasulloLocal.constant_section_iff_pos (X := X) hp)

#print axioms constantSectionSolution

theorem solution :
    ∀ (p X : ℝ), 1 < p →
      ((∃ S : ℂ →L[ℂ] 𝓢(ℝ, ℂ), ∀ c : ℂ,
        Function.Even (S c : ℝ → ℂ) ∧
        S c 0 = 0 ∧ 𝓕 (S c) 0 = 0 ∧
        Function.support (⇑(𝓕 (S c) : 𝓢(ℝ, ℂ))) ⊆ Set.Icc (-(p * X)) (p * X) ∧
        ∀ x : ℝ, (∑' n : ℤ, (S c) (p ^ n * Real.exp x)) = c) ↔ 0 < X) := constantSectionSolution
#print axioms solution
