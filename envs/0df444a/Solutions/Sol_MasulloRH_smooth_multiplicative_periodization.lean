-- Prove2me | solution 1 for MasulloRH.smooth_multiplicative_periodization
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-22T22:12:07.800304+00:00
-- url     : https://prove2.me/submissions/f1768a93-2a7e-4995-a13c-83017796ceef

import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/- Source module: MasulloLocal/OrbitEuler.lean -/
/-!
# The Euler derivative of a logarithmic Schwartz orbit

The actual operator `f ↦ (t ↦ t * f'(t))` is a continuous complex-linear
endomorphism of Schwartz space. Its iterates give the derivative chain for
the multiplicative orbit `x ↦ f(c * exp x)`. No smoothness or derivative
interchange for the periodized sum is asserted here.
-/

open scoped SchwartzMap

set_option autoImplicit false

noncomputable section

namespace MasulloLocal

/-- The Euler differential operator on actual Schwartz space. -/
def orbitEulerCLM : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ (fun t : ℝ => (t : ℂ))).comp
    (SchwartzMap.derivCLM ℂ ℂ)

@[simp]
theorem orbitEulerCLM_apply (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    orbitEulerCLM f t = (t : ℂ) * deriv f t := by
  have hg : (fun t : ℝ => (t : ℂ)).HasTemperateGrowth := by fun_prop
  simp only [orbitEulerCLM, ContinuousLinearMap.comp_apply,
    SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.derivCLM_apply,
    smul_eq_mul]

/-- The Euler operator vanishes at the origin for every Schwartz input. -/
@[simp]
theorem orbitEulerCLM_zero (f : 𝓢(ℝ, ℂ)) : orbitEulerCLM f 0 = 0 := by
  simp

/-- The chain rule for an actual logarithmic orbit, with arbitrary real scale. -/
theorem hasDerivAt_comp_mul_exp (f : 𝓢(ℝ, ℂ)) (c x : ℝ) :
    HasDerivAt (fun y : ℝ => f (c * Real.exp y))
      (orbitEulerCLM f (c * Real.exp x)) x := by
  simpa only [Function.comp_def, orbitEulerCLM_apply, Complex.real_smul] using
    (f.hasDerivAt (c * Real.exp x)).scomp x ((Real.hasDerivAt_exp x).const_mul c)

/-- Integer multiplicative orbits use exactly the same Euler derivative. -/
theorem hasDerivAt_int_orbit_exp (f : 𝓢(ℝ, ℂ)) (p : ℝ) (n : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => f (p ^ n * Real.exp y))
      (orbitEulerCLM f (p ^ n * Real.exp x)) x :=
  hasDerivAt_comp_mul_exp f (p ^ n) x

/-- Continuous iterates of the Euler operator. -/
def orbitEulerIterate : ℕ → 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)
  | 0 => ContinuousLinearMap.id ℂ _
  | j + 1 => orbitEulerCLM.comp (orbitEulerIterate j)

@[simp]
theorem orbitEulerIterate_zero (f : 𝓢(ℝ, ℂ)) : orbitEulerIterate 0 f = f := rfl

@[simp]
theorem orbitEulerIterate_succ_apply (j : ℕ) (f : 𝓢(ℝ, ℂ)) :
    orbitEulerIterate (j + 1) f = orbitEulerCLM (orbitEulerIterate j f) := rfl

/-- Every member of the Euler derivative chain still vanishes at the origin. -/
theorem orbitEulerIterate_apply_zero (j : ℕ) (f : 𝓢(ℝ, ℂ)) (hf0 : f 0 = 0) :
    orbitEulerIterate j f 0 = 0 := by
  cases j with
  | zero => exact hf0
  | succ j => simp

/-- An explicit all-order derivative chain for use in local smooth-series lemmas. -/
theorem hasDerivAt_orbitEulerIterate_exp (j : ℕ) (f : 𝓢(ℝ, ℂ)) (c x : ℝ) :
    HasDerivAt (fun y : ℝ => orbitEulerIterate j f (c * Real.exp y))
      (orbitEulerIterate (j + 1) f (c * Real.exp x)) x :=
  hasDerivAt_comp_mul_exp (orbitEulerIterate j f) c x

#print axioms orbitEulerCLM_apply
#print axioms orbitEulerCLM_zero
#print axioms hasDerivAt_comp_mul_exp
#print axioms hasDerivAt_int_orbit_exp
#print axioms orbitEulerIterate_apply_zero
#print axioms hasDerivAt_orbitEulerIterate_exp

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

/- Source module: MasulloLocal/OrbitUniform.lean -/
/-!
# Uniform bounds for actual multiplicative orbit sums

A Schwartz function vanishing at zero has uniformly summable multiplicative
orbits on every compact logarithmic interval. The two geometric tails use
the weighted value seminorm at infinity and the first derivative seminorm
at zero. No evenness or Fourier-support hypothesis is required.
-/

open scoped SchwartzMap

set_option autoImplicit false

noncomputable section

namespace MasulloLocal

/-- An explicit geometric majorant on a logarithmic interval. -/
def orbitMajorant (p a b : ℝ) (f : 𝓢(ℝ, ℂ)) : ℤ → ℝ :=
  Int.rec
    (fun n => (SchwartzMap.seminorm ℂ 1 0 f / Real.exp a) * (p⁻¹) ^ n)
    (fun n => (SchwartzMap.seminorm ℂ 0 1 f * Real.exp b / p) * (p⁻¹) ^ n)

/-- Both geometric tails of the orbit majorant are summable. -/
theorem summable_orbitMajorant {p : ℝ} (hp : 1 < p) (a b : ℝ)
    (f : 𝓢(ℝ, ℂ)) : Summable (orbitMajorant p a b f) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hgeom := summable_geometric_of_lt_one (inv_nonneg.mpr hp0.le)
    (inv_lt_one_of_one_lt₀ hp)
  exact (hgeom.mul_left (SchwartzMap.seminorm ℂ 1 0 f / Real.exp a)).int_rec
    (hgeom.mul_left (SchwartzMap.seminorm ℂ 0 1 f * Real.exp b / p))

/-- Uniform majorization of an actual orbit on any closed logarithmic interval. -/
theorem norm_orbit_le_majorant {p : ℝ} (hp : 1 < p) (f : 𝓢(ℝ, ℂ))
    (hf0 : f 0 = 0) {a b x : ℝ} (hx : x ∈ Set.Icc a b) (n : ℤ) :
    ‖f (p ^ n * Real.exp x)‖ ≤ orbitMajorant p a b f n := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hS10 : 0 ≤ SchwartzMap.seminorm ℂ 1 0 f := apply_nonneg _ _
  have hS01 : 0 ≤ SchwartzMap.seminorm ℂ 0 1 f := apply_nonneg _ _
  cases n with
  | ofNat n =>
      change ‖f (p ^ (n : ℤ) * Real.exp x)‖ ≤
        (SchwartzMap.seminorm ℂ 1 0 f / Real.exp a) * (p⁻¹) ^ n
      rw [zpow_natCast]
      have hy : 0 < p ^ n * Real.exp x := mul_pos (pow_pos hp0 n) (Real.exp_pos x)
      have hdecay := f.norm_pow_mul_le_seminorm ℂ 1 (p ^ n * Real.exp x)
      rw [pow_one, Real.norm_eq_abs, abs_of_pos hy] at hdecay
      calc
        ‖f (p ^ n * Real.exp x)‖ ≤
            SchwartzMap.seminorm ℂ 1 0 f / (p ^ n * Real.exp x) :=
          (le_div_iff₀ hy).mpr (by simpa only [mul_comm] using hdecay)
        _ = (SchwartzMap.seminorm ℂ 1 0 f / Real.exp x) * (p⁻¹) ^ n := by
          rw [inv_pow]
          field_simp
        _ ≤ (SchwartzMap.seminorm ℂ 1 0 f / Real.exp a) * (p⁻¹) ^ n := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (inv_nonneg.mpr hp0.le) n)
          exact div_le_div_of_nonneg_left hS10 (Real.exp_pos a) (Real.exp_le_exp.mpr hx.1)
  | negSucc n =>
      have hy : 0 < (p⁻¹) ^ (n + 1) * Real.exp x :=
        mul_pos (pow_pos (inv_pos.mpr hp0) (n + 1)) (Real.exp_pos x)
      have h := norm_sub_zero_le_seminorm f ((p⁻¹) ^ (n + 1) * Real.exp x)
      rw [hf0, sub_zero, Real.norm_eq_abs, abs_of_pos hy] at h
      change ‖f (p ^ (Int.negSucc n) * Real.exp x)‖ ≤
        (SchwartzMap.seminorm ℂ 0 1 f * Real.exp b / p) * (p⁻¹) ^ n
      rw [Int.negSucc_eq, zpow_neg, ← Int.natCast_add_one, zpow_natCast, ← inv_pow]
      calc
        ‖f ((p⁻¹) ^ (n + 1) * Real.exp x)‖ ≤
            SchwartzMap.seminorm ℂ 0 1 f * ((p⁻¹) ^ (n + 1) * Real.exp x) := h
        _ = (SchwartzMap.seminorm ℂ 0 1 f * Real.exp x / p) * (p⁻¹) ^ n := by
          rw [pow_succ]
          ring
        _ ≤ (SchwartzMap.seminorm ℂ 0 1 f * Real.exp b / p) * (p⁻¹) ^ n := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (inv_nonneg.mpr hp0.le) n)
          apply div_le_div_of_nonneg_right _ hp0.le
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx.2) hS01

/-- The explicit sum of the two geometric tails. -/
theorem tsum_orbitMajorant {p : ℝ} (hp : 1 < p) (a b : ℝ) (f : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, orbitMajorant p a b f n) =
      (SchwartzMap.seminorm ℂ 1 0 f / Real.exp a +
        SchwartzMap.seminorm ℂ 0 1 f * Real.exp b / p) / (1 - p⁻¹) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hgeom := summable_geometric_of_lt_one (inv_nonneg.mpr hp0.le)
    (inv_lt_one_of_one_lt₀ hp)
  unfold orbitMajorant
  rw [tsum_int_rec (hgeom.mul_left _) (hgeom.mul_left _),
    tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_lt_one (inv_nonneg.mpr hp0.le) (inv_lt_one_of_one_lt₀ hp)]
  ring

/-- A quantitative bound for periodization on any logarithmic interval. -/
theorem norm_periodization_le_on_Icc {p : ℝ} (hp : 1 < p) (f : 𝓢(ℝ, ℂ))
    (hf0 : f 0 = 0) {a b x : ℝ} (hx : x ∈ Set.Icc a b) :
    ‖periodization p f x‖ ≤
      (SchwartzMap.seminorm ℂ 1 0 f / Real.exp a +
        SchwartzMap.seminorm ℂ 0 1 f * Real.exp b / p) / (1 - p⁻¹) := by
  have hb := summable_orbitMajorant hp a b f
  calc
    ‖periodization p f x‖ ≤ ∑' n : ℤ, orbitMajorant p a b f n :=
      tsum_of_norm_bounded hb.hasSum (norm_orbit_le_majorant hp f hf0 hx)
    _ = _ := tsum_orbitMajorant hp a b f

/-- The uniform bound on one full period uses exactly two Schwartz seminorms. -/
theorem norm_periodization_le {p : ℝ} (hp : 1 < p) (f : 𝓢(ℝ, ℂ))
    (hf0 : f 0 = 0) {x : ℝ} (hx : x ∈ Set.Icc 0 (Real.log p)) :
    ‖periodization p f x‖ ≤
      (SchwartzMap.seminorm ℂ 1 0 f + SchwartzMap.seminorm ℂ 0 1 f) / (1 - p⁻¹) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  simpa only [Real.exp_zero, div_one, Real.exp_log hp0, mul_div_cancel_right₀ _ hp0.ne']
    using norm_periodization_le_on_Icc hp f hf0 hx

#print axioms summable_orbitMajorant
#print axioms norm_orbit_le_majorant
#print axioms tsum_orbitMajorant
#print axioms norm_periodization_le_on_Icc
#print axioms norm_periodization_le

end MasulloLocal

/- Source module: MasulloLocal/SeriesOnOpen.lean -/
/-!
# Local smoothness and derivatives of normally convergent series

The functions below are genuine `tsum`s. Uniform summable bounds are required
for every member of an explicit derivative chain on an open preconnected set.
The derivative identities and smoothness of the sum are conclusions, not
assumptions. This local form is suitable for expanding Schwartz orbit series
on a half-line bounded away from zero.
-/

open Set Filter
open scoped Topology ContDiff

set_option autoImplicit false

noncomputable section

namespace MasulloLocal

variable {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable {a : ℕ → ι → ℝ → F} {b : ℕ → ι → ℝ} {s : Set ℝ}

omit [NormedSpace ℝ F] in
/-- Each row of a uniformly summably bounded derivative chain is summable
at every point of its specified domain. -/
theorem summable_derivChain_on
    (hb : ∀ j, Summable (b j))
    (hbound : ∀ j i x, x ∈ s → ‖a j i x‖ ≤ b j i)
    (j : ℕ) {x : ℝ} (hx : x ∈ s) : Summable (fun i => a j i x) :=
  .of_norm_bounded (hb j) (fun i => hbound j i x hx)

/-- A local derivative-of-series statement for an explicit derivative chain. -/
theorem hasDerivAt_tsum_derivChain_on
    (hs : IsOpen s) (hsc : IsPreconnected s)
    (hderiv : ∀ j i x, x ∈ s → HasDerivAt (a j i) (a (j + 1) i x) x)
    (hb : ∀ j, Summable (b j))
    (hbound : ∀ j i x, x ∈ s → ‖a j i x‖ ≤ b j i)
    (j : ℕ) {x : ℝ} (hx : x ∈ s) :
    HasDerivAt (fun y => ∑' i, a j i y) (∑' i, a (j + 1) i x) x := by
  exact hasDerivAt_tsum_of_isPreconnected (hb (j + 1)) hs hsc
    (hderiv j) (hbound (j + 1)) hx
    (summable_derivChain_on hb hbound j hx) hx

/-- Every ordinary iterated derivative of the sum is the corresponding sum
of the derivative chain, locally on the given open set. -/
theorem iteratedDeriv_tsum_derivChain_on
    (hs : IsOpen s) (hsc : IsPreconnected s)
    (hderiv : ∀ j i x, x ∈ s → HasDerivAt (a j i) (a (j + 1) i x) x)
    (hb : ∀ j, Summable (b j))
    (hbound : ∀ j i x, x ∈ s → ‖a j i x‖ ≤ b j i)
    (j : ℕ) {x : ℝ} (hx : x ∈ s) :
    iteratedDeriv j (fun y => ∑' i, a 0 i y) x = ∑' i, a j i x := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv j (fun y => ∑' i, a 0 i y) =ᶠ[𝓝 x]
        (fun y => ∑' i, a j i y) := by
      filter_upwards [hs.mem_nhds hx] with y hy
      exact ih hy
    rw [heq.deriv_eq]
    exact (hasDerivAt_tsum_derivChain_on hs hsc hderiv hb hbound j hx).deriv

/-- The sum of a locally normally convergent derivative chain is smooth on
its open domain. No smoothness of the sum is presupposed. -/
theorem contDiffOn_tsum_derivChain
    (hs : IsOpen s) (hsc : IsPreconnected s)
    (hderiv : ∀ j i x, x ∈ s → HasDerivAt (a j i) (a (j + 1) i x) x)
    (hb : ∀ j, Summable (b j))
    (hbound : ∀ j i x, x ∈ s → ‖a j i x‖ ≤ b j i) :
    ContDiffOn ℝ ∞ (fun y => ∑' i, a 0 i y) s := by
  apply contDiffOn_of_differentiableOn_deriv
  intro j _ x hx
  have heq : iteratedDerivWithin j (fun y => ∑' i, a 0 i y) s =ᶠ[𝓝 x]
      (fun y => ∑' i, a j i y) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    rw [iteratedDerivWithin_of_isOpen hs hy]
    exact iteratedDeriv_tsum_derivChain_on hs hsc hderiv hb hbound j hy
  have hd := hasDerivAt_tsum_derivChain_on hs hsc hderiv hb hbound j hx
  exact (hd.congr_of_eventuallyEq heq).differentiableAt.differentiableWithinAt

variable {f : ι → ℝ → F}

omit [CompleteSpace F] in
/-- The explicit derivative chain used for a dilated smooth function. -/
theorem hasDerivAt_smul_iteratedDeriv_dilation {g : ℝ → F}
    (hg : ContDiff ℝ ∞ g) (c : ℝ) (j : ℕ) (x : ℝ) :
    HasDerivAt (fun y => c ^ j • iteratedDeriv j g (c * y))
      (c ^ (j + 1) • iteratedDeriv (j + 1) g (c * x)) x := by
  have hd := ((hg.differentiable_iteratedDeriv j
    (by exact_mod_cast ENat.natCast_lt_top j)) (c * x)).hasDerivAt
  simpa only [iteratedDeriv_succ, Function.comp_def, mul_one, pow_succ, smul_smul,
    Pi.smul_def] using
    ((hd.scomp x ((hasDerivAt_id x).const_mul c)).const_smul (c ^ j))

/-- Convenient specialization when the individual functions are globally
smooth and the bounds are given for their actual iterated derivatives. -/
theorem iteratedDeriv_tsum_on
    (hs : IsOpen s) (hsc : IsPreconnected s)
    (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hb : ∀ j, Summable (b j))
    (hbound : ∀ j i x, x ∈ s → ‖iteratedDeriv j (f i) x‖ ≤ b j i)
    (j : ℕ) {x : ℝ} (hx : x ∈ s) :
    iteratedDeriv j (fun y => ∑' i, f i y) x = ∑' i, iteratedDeriv j (f i) x := by
  have hderiv : ∀ j i x, x ∈ s → HasDerivAt
      (iteratedDeriv j (f i)) (iteratedDeriv (j + 1) (f i) x) x := by
    intro j i x _
    simpa only [iteratedDeriv_succ] using
      ((hf i).differentiable_iteratedDeriv j
        (by exact_mod_cast ENat.natCast_lt_top j)).differentiableAt.hasDerivAt
  simpa only [iteratedDeriv_zero] using
    iteratedDeriv_tsum_derivChain_on hs hsc hderiv hb hbound j hx

/-- Smooth-family version of the local smooth-series theorem. -/
theorem contDiffOn_tsum_on
    (hs : IsOpen s) (hsc : IsPreconnected s)
    (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hb : ∀ j, Summable (b j))
    (hbound : ∀ j i x, x ∈ s → ‖iteratedDeriv j (f i) x‖ ≤ b j i) :
    ContDiffOn ℝ ∞ (fun y => ∑' i, f i y) s := by
  have hderiv : ∀ j i x, x ∈ s → HasDerivAt
      (iteratedDeriv j (f i)) (iteratedDeriv (j + 1) (f i) x) x := by
    intro j i x _
    simpa only [iteratedDeriv_succ] using
      ((hf i).differentiable_iteratedDeriv j
        (by exact_mod_cast ENat.natCast_lt_top j)).differentiableAt.hasDerivAt
  simpa only [iteratedDeriv_zero] using
    contDiffOn_tsum_derivChain hs hsc hderiv hb hbound

#print axioms iteratedDeriv_tsum_derivChain_on
#print axioms contDiffOn_tsum_derivChain
#print axioms iteratedDeriv_tsum_on
#print axioms contDiffOn_tsum_on
#print axioms hasDerivAt_smul_iteratedDeriv_dilation

end MasulloLocal

/- Source module: MasulloLocal/PeriodizationSmooth.lean -/
/-!
# Smoothness of actual multiplicative periodization

The bilateral orbit sum of a Schwartz function vanishing at the origin is
smooth. Every actual derivative is the orbit sum of the corresponding Euler
derivative. The interchange is proved from summable uniform majorants on a
neighborhood of each logarithmic coordinate; it is not a hypothesis.

Neither evenness nor a Fourier-band or integral condition is needed.
-/

open Set Filter
open scoped SchwartzMap Topology ContDiff

set_option autoImplicit false

noncomputable section

namespace MasulloLocal

/-- Differentiating any member of the actual periodized Euler chain is justified
by uniform summability on a bounded open neighborhood. -/
theorem hasDerivAt_periodization_iterate {p : ℝ} (hp : 1 < p)
    (f : 𝓢(ℝ, ℂ)) (hf0 : f 0 = 0) (j : ℕ) (x : ℝ) :
    HasDerivAt (periodization p (orbitEulerIterate j f))
      (periodization p (orbitEulerIterate (j + 1) f) x) x := by
  let a : ℕ → ℤ → ℝ → ℂ :=
    fun k n y => orbitEulerIterate k f (p ^ n * Real.exp y)
  let b : ℕ → ℤ → ℝ :=
    fun k => orbitMajorant p (x - 1) (x + 1) (orbitEulerIterate k f)
  have hderiv : ∀ k n y, y ∈ Ioo (x - 1) (x + 1) →
      HasDerivAt (a k n) (a (k + 1) n y) y := by
    intro k n y _
    exact hasDerivAt_orbitEulerIterate_exp k f (p ^ n) y
  have hb : ∀ k, Summable (b k) := by
    intro k
    exact summable_orbitMajorant hp (x - 1) (x + 1) (orbitEulerIterate k f)
  have hbound : ∀ k n y, y ∈ Ioo (x - 1) (x + 1) → ‖a k n y‖ ≤ b k n := by
    intro k n y hy
    exact norm_orbit_le_majorant hp (orbitEulerIterate k f)
      (orbitEulerIterate_apply_zero k f hf0) ⟨hy.1.le, hy.2.le⟩ n
  have hx : x ∈ Ioo (x - 1) (x + 1) := by
    constructor <;> linarith
  exact hasDerivAt_tsum_derivChain_on isOpen_Ioo isPreconnected_Ioo
    hderiv hb hbound j hx

/-- All actual iterated derivatives of periodization are the periodized Euler
iterates. This is an identity of functions, not merely a formal jet. -/
theorem iteratedDeriv_periodization {p : ℝ} (hp : 1 < p)
    (f : 𝓢(ℝ, ℂ)) (hf0 : f 0 = 0) (j : ℕ) :
    iteratedDeriv j (periodization p f) =
      periodization p (orbitEulerIterate j f) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (hasDerivAt_periodization_iterate hp f hf0 j x).deriv

/-- The genuine bilateral orbit sum is infinitely differentiable whenever the
Schwartz input vanishes at the additive origin. -/
theorem contDiff_periodization {p : ℝ} (hp : 1 < p)
    (f : 𝓢(ℝ, ℂ)) (hf0 : f 0 = 0) :
    ContDiff ℝ ∞ (periodization p f) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro j _
  rw [iteratedDeriv_periodization hp f hf0 j]
  intro x
  exact (hasDerivAt_periodization_iterate hp f hf0 j x).differentiableAt

/-- The first derivative uses the actual Euler operator. -/
theorem hasDerivAt_periodization {p : ℝ} (hp : 1 < p)
    (f : 𝓢(ℝ, ℂ)) (hf0 : f 0 = 0) (x : ℝ) :
    HasDerivAt (periodization p f) (periodization p (orbitEulerCLM f) x) x := by
  simpa using hasDerivAt_periodization_iterate hp f hf0 0 x

/-- Every derivative is uniformly bounded on one period by two continuous
Schwartz seminorms of the corresponding Euler iterate. -/
theorem norm_iteratedDeriv_periodization_le {p : ℝ} (hp : 1 < p)
    (f : 𝓢(ℝ, ℂ)) (hf0 : f 0 = 0) (j : ℕ)
    {x : ℝ} (hx : x ∈ Icc 0 (Real.log p)) :
    ‖iteratedDeriv j (periodization p f) x‖ ≤
      (SchwartzMap.seminorm ℂ 1 0 (orbitEulerIterate j f) +
        SchwartzMap.seminorm ℂ 0 1 (orbitEulerIterate j f)) / (1 - p⁻¹) := by
  rw [iteratedDeriv_periodization hp f hf0 j]
  exact norm_periodization_le hp (orbitEulerIterate j f)
    (orbitEulerIterate_apply_zero j f hf0) hx

#print axioms hasDerivAt_periodization_iterate
#print axioms iteratedDeriv_periodization
#print axioms contDiff_periodization
#print axioms hasDerivAt_periodization
#print axioms norm_iteratedDeriv_periodization_le

end MasulloLocal

/- Source module: MasulloLocal/PeriodizationContinuous.lean -/
/-!
# Continuous periodization and every actual derivative

The source is the actual closed-origin condition in Schwartz space, with its
inherited topology. The target is continuous functions on the compact circle
with its uniform topology. Every derivative gives a continuous linear map into
this target; the evaluation identity connects those maps to genuine derivatives.
-/

open scoped SchwartzMap NNReal
open Set Function Topology

set_option autoImplicit false

noncomputable section

namespace MasulloLocal

/-- Actual Schwartz functions vanishing at the additive origin. -/
def originZero : Submodule ℂ 𝓢(ℝ, ℂ) where
  carrier := {f | f 0 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro f g hf hg
    change f 0 + g 0 = 0
    rw [hf, hg, add_zero]
  smul_mem' := by
    intro c f hf
    change c • f 0 = 0
    rw [hf, smul_zero]

@[simp] theorem mem_originZero (f : 𝓢(ℝ, ℂ)) : f ∈ originZero ↔ f 0 = 0 := Iff.rfl

/-- The convergent, smooth orbit sum as an actual continuous circle function. -/
def periodizationCircle {p : ℝ} (hp : 1 < p) (f : originZero) :
    C(AddCircle (Real.log p), ℂ) :=
  ⟨(periodization_periodic hp (f : 𝓢(ℝ, ℂ))).lift,
    continuous_coinduced_dom.mpr
      (contDiff_periodization hp (f : 𝓢(ℝ, ℂ)) f.property).continuous⟩

@[simp]
theorem periodizationCircle_apply {p : ℝ} (hp : 1 < p)
    (f : originZero) (x : ℝ) :
    periodizationCircle hp f (x : AddCircle (Real.log p)) =
      periodization p (f : 𝓢(ℝ, ℂ)) x := rfl

/-- The explicit geometric majorant controls the circle's actual supremum norm. -/
theorem norm_periodizationCircle_le {p : ℝ} (hp : 1 < p)
    [Fact (0 < Real.log p)] (f : originZero) :
    ‖periodizationCircle hp f‖ ≤
      (SchwartzMap.seminorm ℂ 1 0 (f : 𝓢(ℝ, ℂ)) +
        SchwartzMap.seminorm ℂ 0 1 (f : 𝓢(ℝ, ℂ))) / (1 - p⁻¹) := by
  have hd : 0 < 1 - p⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hp)
  apply (ContinuousMap.norm_le _ (div_nonneg (add_nonneg (apply_nonneg _ _)
    (apply_nonneg _ _)) hd.le)).mpr
  intro x
  let y := AddCircle.equivIco (Real.log p) 0 x
  have hy : (y : ℝ) ∈ Icc 0 (Real.log p) := by
    have h := y.property
    exact ⟨h.1, by simpa only [zero_add] using h.2.le⟩
  have hx : ((y : ℝ) : AddCircle (Real.log p)) = x := AddCircle.coe_equivIco
  rw [← hx, periodizationCircle_apply]
  exact norm_periodization_le hp (f : 𝓢(ℝ, ℂ)) f.property hy

/-- Periodization is complex-linear because its defining orbit sums converge. -/
def periodizationCircleLM {p : ℝ} (hp : 1 < p) :
    originZero →ₗ[ℂ] C(AddCircle (Real.log p), ℂ) where
  toFun := periodizationCircle hp
  map_add' f g := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      change periodization p ((f : 𝓢(ℝ, ℂ)) + (g : 𝓢(ℝ, ℂ))) x =
        periodization p (f : 𝓢(ℝ, ℂ)) x + periodization p (g : 𝓢(ℝ, ℂ)) x
      exact (periodization_summable hp (f : 𝓢(ℝ, ℂ)) f.property x).tsum_add
        (periodization_summable hp (g : 𝓢(ℝ, ℂ)) g.property x)
  map_smul' c f := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      change (∑' n : ℤ, c • (f : 𝓢(ℝ, ℂ)) (p ^ n * Real.exp x)) =
        c • ∑' n : ℤ, (f : 𝓢(ℝ, ℂ)) (p ^ n * Real.exp x)
      exact Summable.tsum_const_smul c
        (periodization_summable hp (f : 𝓢(ℝ, ℂ)) f.property x)

/-- A reusable continuity criterion using two inherited Schwartz seminorms. -/
theorem continuous_originZero_of_seminorm_bound
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (A : originZero →ₗ[ℂ] G) (C : ℝ≥0)
    (hb : ∀ f, ‖A f‖ ≤ C * (SchwartzMap.seminorm ℂ 1 0 (f : 𝓢(ℝ, ℂ)) +
      SchwartzMap.seminorm ℂ 0 1 (f : 𝓢(ℝ, ℂ)))) : Continuous A := by
  let q : Seminorm ℂ originZero :=
    C • ((SchwartzMap.seminorm ℂ 1 0 + SchwartzMap.seminorm ℂ 0 1).comp
      originZero.subtype)
  have hq : Continuous q := by
    change Continuous (fun f : originZero =>
      (C : ℝ) * (SchwartzMap.seminorm ℂ 1 0 (f : 𝓢(ℝ, ℂ)) +
      SchwartzMap.seminorm ℂ 0 1 (f : 𝓢(ℝ, ℂ))))
    have h10 : Continuous (fun f : originZero =>
        SchwartzMap.seminorm ℂ 1 0 (f : 𝓢(ℝ, ℂ))) :=
      ((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (1, 0)).comp
        continuous_subtype_val
    have h01 : Continuous (fun f : originZero =>
        SchwartzMap.seminorm ℂ 0 1 (f : 𝓢(ℝ, ℂ))) :=
      ((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (0, 1)).comp
        continuous_subtype_val
    exact (h10.add h01).const_mul (C : ℝ)
  apply WithSeminorms.continuous_of_continuous_comp (norm_withSeminorms ℂ G) A
  intro i
  exact Seminorm.continuous_of_le hq hb

/-- The genuine circle-valued periodization map is continuous for the Schwartz
and compact-uniform topologies. -/
def periodizationCircleCLM {p : ℝ} (hp : 1 < p) :
    originZero →L[ℂ] C(AddCircle (Real.log p), ℂ) where
  toLinearMap := periodizationCircleLM hp
  cont := by
    let : Fact (0 < Real.log p) := ⟨Real.log_pos hp⟩
    have hd : 0 < 1 - p⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hp)
    apply continuous_originZero_of_seminorm_bound (periodizationCircleLM hp)
      ⟨(1 - p⁻¹)⁻¹, (inv_pos.mpr hd).le⟩
    intro f
    change ‖periodizationCircle hp f‖ ≤ (1 - p⁻¹)⁻¹ *
      (SchwartzMap.seminorm ℂ 1 0 (f : 𝓢(ℝ, ℂ)) +
        SchwartzMap.seminorm ℂ 0 1 (f : 𝓢(ℝ, ℂ)))
    simpa only [div_eq_mul_inv, mul_comm] using norm_periodizationCircle_le hp f

@[simp]
theorem periodizationCircleCLM_apply {p : ℝ} (hp : 1 < p) (f : originZero) (x : ℝ) :
    periodizationCircleCLM hp f (x : AddCircle (Real.log p)) =
      periodization p (f : 𝓢(ℝ, ℂ)) x := rfl

/-- Euler iterates restrict continuously to functions vanishing at the origin. -/
def originZeroEulerIterate (j : ℕ) : originZero →L[ℂ] originZero :=
  ((orbitEulerIterate j).comp originZero.subtypeL).codRestrict originZero
    (fun f => orbitEulerIterate_apply_zero j (f : 𝓢(ℝ, ℂ)) f.property)

/-- Every actual derivative of periodization is a continuous linear map into
continuous circle functions with their uniform topology. -/
def periodizationDerivativeCLM {p : ℝ} (hp : 1 < p) (j : ℕ) :
    originZero →L[ℂ] C(AddCircle (Real.log p), ℂ) :=
  (periodizationCircleCLM hp).comp (originZeroEulerIterate j)

@[simp]
theorem periodizationDerivativeCLM_apply {p : ℝ} (hp : 1 < p) (j : ℕ)
    (f : originZero) (x : ℝ) :
    periodizationDerivativeCLM hp j f (x : AddCircle (Real.log p)) =
      iteratedDeriv j (periodization p (f : 𝓢(ℝ, ℂ))) x := by
  rw [iteratedDeriv_periodization hp (f : 𝓢(ℝ, ℂ)) f.property j]
  rfl

#print axioms norm_periodizationCircle_le
#print axioms continuous_originZero_of_seminorm_bound
#print axioms periodizationCircleCLM
#print axioms originZeroEulerIterate
#print axioms periodizationDerivativeCLM_apply

end MasulloLocal

/- Source module: MasulloLocal/PeriodicJets.lean -/
/-!
# Smooth circle functions as derivative-compatible continuous jets

The ambient product has the product of the actual continuous-map topologies.
For a nonzero period each factor is a compact circle with its uniform topology.
The submodule below requires each coordinate to be the derivative of the
previous coordinate after pullback to the real line. Its coordinates are
therefore the actual iterated derivatives of one smooth periodic function.

This representation equips smooth circle functions with convergence of every
derivative, rather than only the topology of uniform convergence of values.
-/

open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace MasulloLocal

/-- Compatible continuous jets on a circle. The topology is inherited from
the product of continuous-map spaces. -/
def periodicJets (L : ℝ) : Submodule ℂ (ℕ → C(AddCircle L, ℂ)) where
  carrier := {a | ∀ (j : ℕ) (x : ℝ), HasDerivAt (fun y : ℝ => a j (y : AddCircle L))
    (a (j + 1) (x : AddCircle L)) x}
  zero_mem' := by
    intro j x
    simpa using hasDerivAt_const x (0 : ℂ)
  add_mem' := by
    intro a b ha hb j x
    exact (ha j x).add (hb j x)
  smul_mem' := by
    intro c a ha j x
    exact (ha j x).const_smul c

/-- A jet coordinate pulled back to logarithmic real coordinates. -/
def periodicJetFunction {L : ℝ} (a : periodicJets L) (j : ℕ) : ℝ → ℂ :=
  fun x => (a : ℕ → C(AddCircle L, ℂ)) j (x : AddCircle L)

/-- The compatibility condition is the actual derivative of each coordinate. -/
theorem hasDerivAt_periodicJetFunction {L : ℝ} (a : periodicJets L)
    (j : ℕ) (x : ℝ) :
    HasDerivAt (periodicJetFunction a j) (periodicJetFunction a (j + 1) x) x :=
  a.property j x

/-- Every coordinate is the corresponding ordinary iterated derivative.
No independent formal derivative data can occur in this submodule. -/
theorem iteratedDeriv_periodicJetFunction {L : ℝ} (a : periodicJets L) (j : ℕ) :
    iteratedDeriv j (periodicJetFunction a 0) = periodicJetFunction a j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (hasDerivAt_periodicJetFunction a j x).deriv

/-- The zeroth coordinate is genuinely smooth, as a consequence of compatibility. -/
theorem contDiff_periodicJetFunction {L : ℝ} (a : periodicJets L) :
    ContDiff ℝ ∞ (periodicJetFunction a 0) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro j _
  rw [iteratedDeriv_periodicJetFunction]
  intro x
  exact (hasDerivAt_periodicJetFunction a j x).differentiableAt

/-- Every coordinate is a function with the stated period. -/
theorem periodic_periodicJetFunction {L : ℝ} (a : periodicJets L) (j : ℕ) :
    Function.Periodic (periodicJetFunction a j) L := by
  intro x
  simp only [periodicJetFunction, AddCircle.coe_add_period]

/-- The defining compatibility condition, exposed for continuous-map restriction. -/
theorem mem_periodicJets {L : ℝ} (a : ℕ → C(AddCircle L, ℂ)) :
    a ∈ periodicJets L ↔
      ∀ (j : ℕ) (x : ℝ), HasDerivAt (fun y : ℝ => a j (y : AddCircle L))
        (a (j + 1) (x : AddCircle L)) x := Iff.rfl

/-- A compatible jet is uniquely determined by its actual underlying function. -/
theorem periodicJets_ext {L : ℝ} (a b : periodicJets L)
    (h : periodicJetFunction a 0 = periodicJetFunction b 0) : a = b := by
  apply Subtype.ext
  funext j
  ext z
  induction z using QuotientAddGroup.induction_on with
  | H x =>
    change periodicJetFunction a j x = periodicJetFunction b j x
    rw [← iteratedDeriv_periodicJetFunction a j,
      ← iteratedDeriv_periodicJetFunction b j, h]

#print axioms iteratedDeriv_periodicJetFunction
#print axioms contDiff_periodicJetFunction
#print axioms periodic_periodicJetFunction
#print axioms periodicJets_ext

end MasulloLocal

/- Source module: MasulloLocal/PeriodizationJets.lean -/
/-!
# Actual smooth periodization as a continuous linear map

The orbit sum and every derivative are assembled into a compatible continuous
jet. Its inherited topology records uniform convergence of every derivative
on the circle. Compatibility is proved from differentiation of the actual
convergent series, rather than imposed as an assumption on the input.
-/

open scoped SchwartzMap ContDiff

set_option autoImplicit false

noncomputable section

namespace MasulloLocal

/-- The continuous linear map containing all actual orbit-sum derivatives. -/
def periodizationJetCLM {p : ℝ} (hp : 1 < p) :
    originZero →L[ℂ] (ℕ → C(AddCircle (Real.log p), ℂ)) :=
  ContinuousLinearMap.pi (periodizationDerivativeCLM hp)

@[simp]
theorem periodizationJetCLM_apply {p : ℝ} (hp : 1 < p)
    (f : originZero) (j : ℕ) (x : ℝ) :
    periodizationJetCLM hp f j (x : AddCircle (Real.log p)) =
      iteratedDeriv j (periodization p (f : 𝓢(ℝ, ℂ))) x :=
  periodizationDerivativeCLM_apply hp j f x

/-- The continuous jet has the actual derivative compatibility condition. -/
theorem periodizationJetCLM_mem {p : ℝ} (hp : 1 < p) (f : originZero) :
    periodizationJetCLM hp f ∈ periodicJets (Real.log p) := by
  intro j x
  change HasDerivAt (periodization p (orbitEulerIterate j (f : 𝓢(ℝ, ℂ))))
    (periodization p (orbitEulerIterate (j + 1) (f : 𝓢(ℝ, ℂ))) x) x
  exact hasDerivAt_periodization_iterate hp (f : 𝓢(ℝ, ℂ)) f.property j x

/-- Periodization with its genuine smooth codomain and all-derivative topology. -/
def smoothPeriodizationCLM {p : ℝ} (hp : 1 < p) :
    originZero →L[ℂ] periodicJets (Real.log p) :=
  (periodizationJetCLM hp).codRestrict (periodicJets (Real.log p))
    (periodizationJetCLM_mem hp)

/-- The smooth-map construction records precisely the actual derivatives. -/
theorem smoothPeriodizationCLM_function {p : ℝ} (hp : 1 < p)
    (f : originZero) (j : ℕ) :
    periodicJetFunction (smoothPeriodizationCLM hp f) j =
      iteratedDeriv j (periodization p (f : 𝓢(ℝ, ℂ))) := by
  funext x
  exact periodizationJetCLM_apply hp f j x

/-- Its underlying function is exactly the bilateral orbit sum. -/
@[simp]
theorem smoothPeriodizationCLM_function_zero {p : ℝ} (hp : 1 < p)
    (f : originZero) :
    periodicJetFunction (smoothPeriodizationCLM hp f) 0 =
      periodization p (f : 𝓢(ℝ, ℂ)) := by
  simpa only [iteratedDeriv_zero] using smoothPeriodizationCLM_function hp f 0

#print axioms periodizationJetCLM
#print axioms periodizationJetCLM_mem
#print axioms smoothPeriodizationCLM
#print axioms smoothPeriodizationCLM_function

end MasulloLocal

/- Source module: Publication/SmoothPeriodizationSolution.lean -/
open scoped SchwartzMap ContDiff

set_option autoImplicit false

noncomputable section

/-- A public statement using only upstream Schwartz, derivative, quotient,
continuous-map, and continuous-linear-map definitions. The source is literally
the kernel of evaluation at the additive origin. -/
theorem smoothPeriodizationSolution :
    ∀ (p : ℝ), 1 < p →
      let Z : Submodule ℂ 𝓢(ℝ, ℂ) :=
        ((BoundedContinuousFunction.evalCLM ℂ (0 : ℝ)).comp
          (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)).ker
      ∃ J : Z →L[ℂ] (ℕ → C(AddCircle (Real.log p), ℂ)),
        ∀ f : Z,
          ContDiff ℝ ∞ (fun x : ℝ =>
            ∑' n : ℤ, (f : 𝓢(ℝ, ℂ)) (p ^ n * Real.exp x)) ∧
          Function.Periodic (fun x : ℝ =>
            ∑' n : ℤ, (f : 𝓢(ℝ, ℂ)) (p ^ n * Real.exp x)) (Real.log p) ∧
          ∀ (j : ℕ) (x : ℝ),
            J f j (x : AddCircle (Real.log p)) =
              iteratedDeriv j (fun y : ℝ =>
                ∑' n : ℤ, (f : 𝓢(ℝ, ℂ)) (p ^ n * Real.exp y)) x := by
  intro p hp
  change ∃ J : MasulloLocal.originZero →L[ℂ] (ℕ → C(AddCircle (Real.log p), ℂ)),
    ∀ f : MasulloLocal.originZero,
      ContDiff ℝ ∞ (MasulloLocal.periodization p (f : 𝓢(ℝ, ℂ))) ∧
      Function.Periodic (MasulloLocal.periodization p (f : 𝓢(ℝ, ℂ))) (Real.log p) ∧
      ∀ (j : ℕ) (x : ℝ), J f j (x : AddCircle (Real.log p)) =
        iteratedDeriv j (MasulloLocal.periodization p (f : 𝓢(ℝ, ℂ))) x
  refine ⟨MasulloLocal.periodizationJetCLM hp, fun f => ⟨?_, ?_, ?_⟩⟩
  · exact MasulloLocal.contDiff_periodization hp (f : 𝓢(ℝ, ℂ)) f.property
  · exact MasulloLocal.periodization_periodic hp (f : 𝓢(ℝ, ℂ))
  · exact MasulloLocal.periodizationJetCLM_apply hp f

#print axioms smoothPeriodizationSolution

theorem solution :
    ∀ (p : ℝ), 1 < p →
      let Z : Submodule ℂ 𝓢(ℝ, ℂ) :=
        ((BoundedContinuousFunction.evalCLM ℂ (0 : ℝ)).comp
          (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)).ker
      ∃ J : Z →L[ℂ] (ℕ → C(AddCircle (Real.log p), ℂ)),
        ∀ f : Z,
          ContDiff ℝ ∞ (fun x : ℝ =>
            ∑' n : ℤ, (f : 𝓢(ℝ, ℂ)) (p ^ n * Real.exp x)) ∧
          Function.Periodic (fun x : ℝ =>
            ∑' n : ℤ, (f : 𝓢(ℝ, ℂ)) (p ^ n * Real.exp x)) (Real.log p) ∧
          ∀ (j : ℕ) (x : ℝ),
            J f j (x : AddCircle (Real.log p)) =
              iteratedDeriv j (fun y : ℝ =>
                ∑' n : ℤ, (f : 𝓢(ℝ, ℂ)) (p ^ n * Real.exp y)) x := smoothPeriodizationSolution
#print axioms solution
