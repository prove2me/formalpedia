-- Prove2me | solution 1 for MasulloRH.one_prime_fourier_band_kernel_exactness
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-22T20:55:35.357873+00:00
-- url     : https://prove2.me/submissions/e72397a8-2862-43f6-aec3-988c0e50982d

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
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Module

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

/- Source module: MasulloLocal/KernelSeries.lean -/
/-!
# The actual contracting preimage of the dilation difference

The candidate is defined as a convergent series of actual Schwartz values.
This module does not assume that the candidate is smooth or Schwartz; those
properties must be established separately before applying the support-drop theorem.
-/

open scoped SchwartzMap FourierTransform
open MeasureTheory Filter Topology

set_option autoImplicit false

noncomputable section

namespace MasulloLocal

/-- The contracting preimage, with the origin value subtracted in every term. -/
def contractingPrimitive (p : ℝ) (f : 𝓢(ℝ, ℂ)) (t : ℝ) : ℂ :=
  -∑' n : ℕ, (f ((p⁻¹) ^ (n + 1) * t) - f 0)

/-- Contracting orbit summability for every real argument, including zero and negative ones. -/
theorem summable_nat_contract_sub_zero_real {p : ℝ} (hp : 1 < p)
    (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    Summable (fun n : ℕ => f ((p⁻¹) ^ n * t) - f 0) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hgeom := summable_geometric_of_lt_one (inv_nonneg.mpr hp0.le)
    (inv_lt_one_of_one_lt₀ hp)
  apply (hgeom.mul_left (SchwartzMap.seminorm ℂ 0 1 f * |t|)).of_norm_bounded
  intro n
  have h := norm_sub_zero_le_seminorm f ((p⁻¹) ^ n * t)
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hp0.le) n)] at h
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

theorem summable_contractingPrimitive {p : ℝ} (hp : 1 < p)
    (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    Summable (fun n : ℕ => f ((p⁻¹) ^ (n + 1) * t) - f 0) :=
  (summable_nat_contract_sub_zero_real hp f t).comp_injective Nat.succ_injective

@[simp] theorem contractingPrimitive_zero (p : ℝ) (f : 𝓢(ℝ, ℂ)) :
    contractingPrimitive p f 0 = 0 := by
  simp only [contractingPrimitive, mul_zero, sub_self, tsum_zero, neg_zero]

/-- Evenness is inherited from the original Schwartz function. -/
theorem contractingPrimitive_even (p : ℝ) (f : 𝓢(ℝ, ℂ))
    (hf : Function.Even (f : ℝ → ℂ)) : Function.Even (contractingPrimitive p f) := by
  intro t
  unfold contractingPrimitive
  congr 1
  apply tsum_congr
  intro n
  rw [mul_neg, hf ((p⁻¹) ^ (n + 1) * t)]

/-- The genuine pointwise dilation equation, with its exact origin correction. -/
theorem contractingPrimitive_euler_eq {p : ℝ} (hp : 1 < p)
    (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    contractingPrimitive p f t - contractingPrimitive p f (p * t) = f t - f 0 := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  let a : ℕ → ℂ := fun n => f ((p⁻¹) ^ n * t) - f 0
  have hs : Summable a := summable_nat_contract_sub_zero_real hp f t
  have hfirst : contractingPrimitive p f t = -∑' n : ℕ, a (n + 1) := rfl
  have hshift : contractingPrimitive p f (p * t) = -∑' n : ℕ, a n := by
    unfold contractingPrimitive
    congr 1
    apply tsum_congr
    intro n
    have hm : (p⁻¹) ^ (n + 1) * (p * t) = (p⁻¹) ^ n * t := by
      calc
        (p⁻¹) ^ (n + 1) * (p * t)
            = (p⁻¹ * p) * ((p⁻¹) ^ n * t) := by rw [pow_succ]; ring
        _ = (p⁻¹) ^ n * t := by rw [inv_mul_cancel₀ hp0.ne', one_mul]
    rw [hm]
  rw [hfirst, hshift, hs.tsum_eq_zero_add]
  simp only [a, pow_zero, one_mul]
  ring

theorem contractingPrimitive_euler_eq_of_zero {p : ℝ} (hp : 1 < p)
    (f : 𝓢(ℝ, ℂ)) (hf0 : f 0 = 0) (t : ℝ) :
    contractingPrimitive p f t - contractingPrimitive p f (p * t) = f t := by
  rw [contractingPrimitive_euler_eq hp, hf0, sub_zero]

/-- On a positive orbit, vanishing periodization identifies the contracting preimage
with the expanding Schwartz series. No evenness hypothesis is needed here. -/
theorem contractingPrimitive_eq_expanding_pos {p t : ℝ} (hp : 1 < p) (ht : 0 < t)
    (f : 𝓢(ℝ, ℂ)) (hf0 : f 0 = 0)
    (hP : ∀ x : ℝ, periodization p f x = 0) :
    contractingPrimitive p f t = ∑' n : ℕ, f (p ^ n * t) := by
  have hspos : Summable (fun n : ℕ => f (p ^ (n : ℤ) * t)) :=
    by simpa only [zpow_natCast] using summable_nat_orbit hp ht f
  have hsneg : Summable (fun n : ℕ => f (p ^ (-((n : ℤ) + 1)) * t)) := by
    simpa only [hf0, sub_zero, zpow_neg, ← Int.natCast_add_one,
      zpow_natCast, inv_pow] using summable_contractingPrimitive hp f t
  have hsplit := tsum_of_nat_of_neg_add_one
    (f := fun n : ℤ => f (p ^ n * t)) hspos hsneg
  have htotal : (∑' n : ℤ, f (p ^ n * t)) = 0 := by
    simpa only [periodization, Real.exp_log ht] using hP (Real.log t)
  rw [htotal] at hsplit
  have hsplit' : (0 : ℂ) = (∑' n : ℕ, f (p ^ n * t)) +
      ∑' n : ℕ, f ((p⁻¹) ^ (n + 1) * t) := by
    simpa only [zpow_neg, ← Int.natCast_add_one, zpow_natCast, ← inv_pow] using hsplit
  have h := congrArg
    (fun z : ℂ => z - ∑' n : ℕ, f ((p⁻¹) ^ (n + 1) * t)) hsplit'
  simpa only [contractingPrimitive, hf0, sub_zero, zero_sub, add_sub_cancel_right] using h

/-- Evenness transfers the expanding-series identification to every nonzero real argument. -/
theorem contractingPrimitive_eq_expanding_of_periodization_zero {p t : ℝ}
    (hp : 1 < p) (ht : t ≠ 0) (f : 𝓢(ℝ, ℂ))
    (hfe : Function.Even (f : ℝ → ℂ)) (hf0 : f 0 = 0)
    (hP : ∀ x : ℝ, periodization p f x = 0) :
    contractingPrimitive p f t = ∑' n : ℕ, f (p ^ n * t) := by
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · calc
      contractingPrimitive p f t = contractingPrimitive p f (-t) :=
        (contractingPrimitive_even p f hfe t).symm
      _ = ∑' n : ℕ, f (p ^ n * (-t)) :=
        contractingPrimitive_eq_expanding_pos hp (neg_pos.mpr hneg) f hf0 hP
      _ = ∑' n : ℕ, f (p ^ n * t) := by
        apply tsum_congr
        intro n
        rw [mul_neg, hfe (p ^ n * t)]
  · exact contractingPrimitive_eq_expanding_pos hp hpos f hf0 hP

#print axioms summable_contractingPrimitive
#print axioms contractingPrimitive_euler_eq
#print axioms contractingPrimitive_eq_expanding_of_periodization_zero

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

/- Source module: MasulloLocal/ContractSmooth.lean -/
/-!
# Smoothness of the actual contracting preimage

The centered summands do not have a summable bound uniform on the whole real
line. We instead differentiate them using convergence at zero and a globally
summable first-derivative bound. All derivatives of that derivative series do
have globally summable bounds.
-/

open scoped SchwartzMap FourierTransform ContDiff
open MeasureTheory Filter Topology

set_option autoImplicit false

noncomputable section

namespace MasulloLocal

/-- A contraction with a scalar prefactor has summable bounds at every order. -/
theorem norm_iteratedFDeriv_scaled_schwartz_le
    (h : 𝓢(ℝ, ℂ)) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (k : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ k (fun x : ℝ => a • h (a * x)) t‖ ≤
      a * SchwartzMap.seminorm ℂ 0 k h := by
  have hcomp : ContDiff ℝ (k : ℕ) (fun x : ℝ => h (a * x)) :=
    (h.smooth k).comp (contDiff_const.mul contDiff_id)
  rw [iteratedFDeriv_const_smul_apply' hcomp.contDiffAt]
  have hscale := congrFun (iteratedFDeriv_comp_const_smul a (h.smooth k)) t
  simp only [smul_eq_mul] at hscale
  rw [hscale, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha0,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ha0 k)]
  calc
    a * (a ^ k * ‖iteratedFDeriv ℝ k h (a * t)‖)
        ≤ a * (1 * ‖iteratedFDeriv ℝ k h (a * t)‖) := by
          gcongr
          exact pow_le_one₀ ha0 ha1
    _ = a * ‖iteratedFDeriv ℝ k h (a * t)‖ := by rw [one_mul]
    _ ≤ a * SchwartzMap.seminorm ℂ 0 k h :=
      mul_le_mul_of_nonneg_left (h.norm_iteratedFDeriv_le_seminorm ℂ k (a * t)) ha0

/-- The weighted contracting series of an arbitrary Schwartz function is smooth. -/
theorem contDiff_tsum_contract_scaled {p : ℝ} (hp : 1 < p) (h : 𝓢(ℝ, ℂ)) :
    ContDiff ℝ ∞ (fun t : ℝ =>
      ∑' n : ℕ, (p⁻¹) ^ (n + 1) • h ((p⁻¹) ^ (n + 1) * t)) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hr0 : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0.le
  have hr1 : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  have hgeom : Summable (fun n : ℕ => (p⁻¹) ^ (n + 1)) :=
    (summable_geometric_of_lt_one hr0 hr1).comp_injective Nat.succ_injective
  refine contDiff_tsum
    (v := fun k n => (p⁻¹) ^ (n + 1) * SchwartzMap.seminorm ℂ 0 k h)
    (N := ⊤) ?_ ?_ ?_
  · intro n
    exact ((h.smooth ⊤).comp (contDiff_const.mul contDiff_id)).const_smul _
  · intro k _
    exact hgeom.mul_right _
  · intro k n t _
    exact norm_iteratedFDeriv_scaled_schwartz_le h
      (pow_nonneg hr0 _) (pow_le_one₀ hr0 hr1.le) k t

/-- Every derivative of the weighted contracting series is its actual derivative series. -/
theorem iteratedDeriv_tsum_contract_scaled {p : ℝ} (hp : 1 < p)
    (h : 𝓢(ℝ, ℂ)) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun y : ℝ =>
      ∑' n : ℕ, (p⁻¹) ^ (n + 1) • h ((p⁻¹) ^ (n + 1) * y)) t =
    ∑' n : ℕ, ((p⁻¹) ^ (n + 1)) ^ (k + 1) •
      iteratedDeriv k h ((p⁻¹) ^ (n + 1) * t) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hr0 : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0.le
  have hr1 : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  have hgeom : Summable (fun n : ℕ => (p⁻¹) ^ (n + 1)) :=
    (summable_geometric_of_lt_one hr0 hr1).comp_injective Nat.succ_injective
  have hF := iteratedFDeriv_tsum_apply
    (f := fun n : ℕ => fun y : ℝ =>
      (p⁻¹) ^ (n + 1) • h ((p⁻¹) ^ (n + 1) * y))
    (v := fun j n => (p⁻¹) ^ (n + 1) * SchwartzMap.seminorm ℂ 0 j h)
    (N := ⊤)
    (fun n => ((h.smooth ⊤).comp (contDiff_const.mul contDiff_id)).const_smul _)
    (fun j _ => hgeom.mul_right _)
    (fun j n y _ => norm_iteratedFDeriv_scaled_schwartz_le h
      (pow_nonneg hr0 _) (pow_le_one₀ hr0 hr1.le) j y)
    (k := k) (by simp) t
  let e := (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) ℂ).symm.toContinuousLinearEquiv
  have he := congrArg e hF
  rw [e.map_tsum] at he
  change iteratedDeriv k (fun y : ℝ =>
      ∑' n : ℕ, (p⁻¹) ^ (n + 1) • h ((p⁻¹) ^ (n + 1) * y)) t =
    ∑' n : ℕ, iteratedDeriv k
      (fun y : ℝ => (p⁻¹) ^ (n + 1) • h ((p⁻¹) ^ (n + 1) * y)) t at he
  rw [he]
  apply tsum_congr
  intro n
  rw [iteratedDeriv_fun_const_smul_field,
    iteratedDeriv_comp_const_smul (h.smooth k) ((p⁻¹) ^ (n + 1))]
  simp only [smul_smul, ← pow_succ']

/-- First derivative of the contracting preimage, with its exact sign. -/
theorem hasDerivAt_contractingPrimitive {p : ℝ} (hp : 1 < p)
    (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    HasDerivAt (contractingPrimitive p f)
      (-(∑' n : ℕ, (p⁻¹) ^ (n + 1) •
        deriv f ((p⁻¹) ^ (n + 1) * t))) t := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hr0 : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0.le
  have hr1 : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  have hgeom : Summable (fun n : ℕ => (p⁻¹) ^ (n + 1)) :=
    (summable_geometric_of_lt_one hr0 hr1).comp_injective Nat.succ_injective
  have hsum := hasDerivAt_tsum
    (g := fun n : ℕ => fun y : ℝ => f ((p⁻¹) ^ (n + 1) * y) - f 0)
    (g' := fun n : ℕ => fun y : ℝ =>
      (p⁻¹) ^ (n + 1) • deriv f ((p⁻¹) ^ (n + 1) * y))
    (u := fun n : ℕ => (p⁻¹) ^ (n + 1) * SchwartzMap.seminorm ℂ 0 1 f)
    (y₀ := 0) (hgeom.mul_right _) ?_ ?_ ?_ t
  · exact hsum.neg
  · intro n y
    simpa only [Function.comp_def, mul_one] using
      ((f.hasDerivAt ((p⁻¹) ^ (n + 1) * y)).scomp y
        ((hasDerivAt_id y).const_mul ((p⁻¹) ^ (n + 1)))).sub_const (f 0)
  · intro n y
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr0 _)]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr0 _)
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one] using
      f.norm_iteratedFDeriv_le_seminorm ℂ 1 ((p⁻¹) ^ (n + 1) * y)
  · simp only [mul_zero, sub_self, summable_zero]

theorem deriv_contractingPrimitive {p : ℝ} (hp : 1 < p)
    (f : 𝓢(ℝ, ℂ)) :
    deriv (contractingPrimitive p f) = fun t : ℝ =>
      -(∑' n : ℕ, (p⁻¹) ^ (n + 1) •
        deriv f ((p⁻¹) ^ (n + 1) * t)) :=
  funext (fun t => (hasDerivAt_contractingPrimitive hp f t).deriv)

/-- The contracting preimage is globally smooth, including at the origin. -/
theorem contDiff_contractingPrimitive {p : ℝ} (hp : 1 < p)
    (f : 𝓢(ℝ, ℂ)) :
    ContDiff ℝ ∞ (contractingPrimitive p f) := by
  apply contDiff_infty_iff_deriv.mpr
  constructor
  · intro t
    exact (hasDerivAt_contractingPrimitive hp f t).differentiableAt
  · rw [deriv_contractingPrimitive hp f]
    exact (contDiff_tsum_contract_scaled hp (SchwartzMap.derivCLM ℂ ℂ f)).neg

/-- All positive-order derivatives of the contracting primitive, with the exact
contraction power and sign. -/
theorem iteratedDeriv_contractingPrimitive_succ {p : ℝ} (hp : 1 < p)
    (f : 𝓢(ℝ, ℂ)) (k : ℕ) (t : ℝ) :
    iteratedDeriv (k + 1) (contractingPrimitive p f) t =
      -(∑' n : ℕ, ((p⁻¹) ^ (n + 1)) ^ (k + 1) •
        iteratedDeriv (k + 1) f ((p⁻¹) ^ (n + 1) * t)) := by
  rw [iteratedDeriv_succ', deriv_contractingPrimitive hp f, iteratedDeriv_fun_neg]
  have h := iteratedDeriv_tsum_contract_scaled hp (SchwartzMap.derivCLM ℂ ℂ f) k t
  change iteratedDeriv k (fun y : ℝ =>
      ∑' n : ℕ, (p⁻¹) ^ (n + 1) • deriv f ((p⁻¹) ^ (n + 1) * y)) t =
    ∑' n : ℕ, ((p⁻¹) ^ (n + 1)) ^ (k + 1) •
      iteratedDeriv k (deriv f) ((p⁻¹) ^ (n + 1) * t) at h
  rw [h, iteratedDeriv_succ']

#print axioms norm_iteratedFDeriv_scaled_schwartz_le
#print axioms contDiff_tsum_contract_scaled
#print axioms iteratedDeriv_tsum_contract_scaled
#print axioms hasDerivAt_contractingPrimitive
#print axioms deriv_contractingPrimitive
#print axioms contDiff_contractingPrimitive
#print axioms iteratedDeriv_contractingPrimitive_succ

end MasulloLocal

/- Source module: MasulloLocal/ExpandingBounds.lean -/
open scoped SchwartzMap
open MeasureTheory
set_option autoImplicit false
noncomputable section
namespace MasulloLocal

/-- The actual order-j derivative of the n-th expanding orbit summand. -/
def expandingDerivTerm (p : ℝ) (f : 𝓢(ℝ, ℂ)) (j n : ℕ) (t : ℝ) : ℂ :=
  (p ^ n) ^ j • iteratedDeriv j f (p ^ n * t)

theorem norm_expandingDerivTerm {p : ℝ} (hp : 0 ≤ p)
    (f : 𝓢(ℝ, ℂ)) (j n : ℕ) (t : ℝ) :
    ‖expandingDerivTerm p f j n t‖ =
      (p ^ n) ^ j * ‖iteratedDeriv j f (p ^ n * t)‖ := by
  simp only [expandingDerivTerm, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (pow_nonneg hp n) j)]

/-- A geometric majorant uniform on any set separated from the additive origin. -/
theorem norm_expandingDerivTerm_le {p ε t : ℝ} (hp : 1 < p)
    (hε : 0 < ε) (ht : ε ≤ |t|) (f : 𝓢(ℝ, ℂ)) (j n : ℕ) :
    ‖expandingDerivTerm p f j n t‖ ≤
      (SchwartzMap.seminorm ℂ (j + 1) j f / ε ^ (j + 1)) * (p⁻¹) ^ n := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hr : 0 < p ^ n := pow_pos hp0 n
  have hpow : ε ^ (j + 1) ≤ |t| ^ (j + 1) :=
    pow_le_pow_left₀ hε.le ht _
  have hb := SchwartzMap.le_seminorm' ℂ (j + 1) j f (p ^ n * t)
  rw [abs_mul, abs_of_pos hr, mul_pow] at hb
  rw [norm_expandingDerivTerm hp0.le]
  have hmul :
      ((p ^ n) ^ j * ‖iteratedDeriv j f (p ^ n * t)‖) *
        (p ^ n * ε ^ (j + 1)) ≤ SchwartzMap.seminorm ℂ (j + 1) j f := by
    calc
      _ = (p ^ n) ^ (j + 1) * ε ^ (j + 1) *
          ‖iteratedDeriv j f (p ^ n * t)‖ := by rw [pow_succ]; ring
      _ ≤ (p ^ n) ^ (j + 1) * |t| ^ (j + 1) *
          ‖iteratedDeriv j f (p ^ n * t)‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpow (pow_nonneg hr.le _)) (norm_nonneg _)
      _ ≤ _ := hb
  calc
    _ ≤ SchwartzMap.seminorm ℂ (j + 1) j f / (p ^ n * ε ^ (j + 1)) :=
      (le_div_iff₀ (mul_pos hr (pow_pos hε _))).mpr hmul
    _ = _ := by rw [inv_pow]; field_simp

/-- With polynomial physical weight, the expanding derivative terms still have a
summable geometric majorant on the exterior region. -/
theorem weighted_norm_expandingDerivTerm_le {p t : ℝ} (hp : 1 < p)
    (ht : 1 ≤ |t|) (f : 𝓢(ℝ, ℂ)) (k j n : ℕ) :
    |t| ^ k * ‖expandingDerivTerm p f j n t‖ ≤
      SchwartzMap.seminorm ℂ (k + j + 1) j f * (p⁻¹) ^ n := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hr : 0 < p ^ n := pow_pos hp0 n
  have hr1 : 1 ≤ p ^ n := one_le_pow₀ hp.le
  have hfac : 1 ≤ (p ^ n) ^ k * |t| ^ (j + 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hr1) (one_le_pow₀ ht)
  have hb := SchwartzMap.le_seminorm' ℂ (k + j + 1) j f (p ^ n * t)
  rw [abs_mul, abs_of_pos hr, mul_pow] at hb
  rw [norm_expandingDerivTerm hp0.le]
  have hmul :
      (|t| ^ k * ((p ^ n) ^ j * ‖iteratedDeriv j f (p ^ n * t)‖)) * p ^ n ≤
        SchwartzMap.seminorm ℂ (k + j + 1) j f := by
    calc
      _ ≤ ((p ^ n) ^ k * |t| ^ (j + 1)) *
          ((|t| ^ k * ((p ^ n) ^ j * ‖iteratedDeriv j f (p ^ n * t)‖)) * p ^ n) :=
            le_mul_of_one_le_left (by positivity) hfac
      _ = (p ^ n) ^ (k + j + 1) * |t| ^ (k + j + 1) *
          ‖iteratedDeriv j f (p ^ n * t)‖ := by simp only [pow_add, pow_one]; ring
      _ ≤ _ := hb
  calc
    _ ≤ SchwartzMap.seminorm ℂ (k + j + 1) j f / p ^ n :=
      (le_div_iff₀ hr).mpr hmul
    _ = _ := by rw [div_eq_mul_inv, inv_pow]

/-- Absolute convergence of every expanding derivative series away from zero. -/
theorem summable_expandingDerivTerm {p t : ℝ} (hp : 1 < p) (ht : t ≠ 0)
    (f : 𝓢(ℝ, ℂ)) (j : ℕ) :
    Summable (fun n : ℕ => expandingDerivTerm p f j n t) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hgeom := summable_geometric_of_lt_one (inv_nonneg.mpr hp0.le)
    (inv_lt_one_of_one_lt₀ hp)
  exact (hgeom.mul_left (SchwartzMap.seminorm ℂ (j + 1) j f / |t| ^ (j + 1))).of_norm_bounded
    (fun n => norm_expandingDerivTerm_le hp (abs_pos.mpr ht) le_rfl f j n)

/-- A uniform exterior Schwartz bound for the actual sum of expanding derivatives. -/
theorem weighted_norm_tsum_expandingDerivTerm_le {p t : ℝ} (hp : 1 < p)
    (ht : 1 ≤ |t|) (f : 𝓢(ℝ, ℂ)) (k j : ℕ) :
    |t| ^ k * ‖∑' n : ℕ, expandingDerivTerm p f j n t‖ ≤
      ∑' n : ℕ, SchwartzMap.seminorm ℂ (k + j + 1) j f * (p⁻¹) ^ n := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have ht0 : t ≠ 0 := by
    intro h
    simp only [h, abs_zero] at ht
    linarith
  have hs := summable_expandingDerivTerm hp ht0 f j
  have hg := (summable_geometric_of_lt_one (inv_nonneg.mpr hp0.le)
    (inv_lt_one_of_one_lt₀ hp)).mul_left (SchwartzMap.seminorm ℂ (k + j + 1) j f)
  have hb := tsum_of_norm_bounded hg.hasSum
    (fun n => (show ‖|t| ^ k • expandingDerivTerm p f j n t‖ ≤
      SchwartzMap.seminorm ℂ (k + j + 1) j f * (p⁻¹) ^ n by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg t) k)]
        exact weighted_norm_expandingDerivTerm_le hp ht f k j n))
  rw [Summable.tsum_const_smul (|t| ^ k) hs, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (abs_nonneg t) k)] at hb
  exact hb

#print axioms norm_expandingDerivTerm_le
#print axioms weighted_norm_expandingDerivTerm_le
#print axioms summable_expandingDerivTerm
#print axioms weighted_norm_tsum_expandingDerivTerm_le
end MasulloLocal

/- Source module: MasulloLocal/ExpandingSmooth.lean -/
/-!
# Actual derivatives of the expanding orbit series

The expanding series and all its derivative series converge locally normally
away from zero. The local calculus theorem is instantiated with explicit
Schwartz seminorm bounds. Under the actual periodization-kernel condition,
the contracting primitive has these same derivatives away from zero.
-/

open Set Filter
open scoped Topology SchwartzMap ContDiff

set_option autoImplicit false

noncomputable section

namespace MasulloLocal

/-- The displayed expanding derivative terms form an actual derivative chain. -/
theorem hasDerivAt_expandingDerivTerm (p : ℝ) (f : 𝓢(ℝ, ℂ))
    (j n : ℕ) (t : ℝ) :
    HasDerivAt (expandingDerivTerm p f j n)
      (expandingDerivTerm p f (j + 1) n t) t :=
  hasDerivAt_smul_iteratedDeriv_dilation (f.smooth ⊤) (p ^ n) j t

/-- All derivatives may be passed through the actual expanding orbit sum on
an open preconnected domain uniformly separated from zero. -/
theorem iteratedDeriv_tsum_expanding_on {p ε t : ℝ} {s : Set ℝ}
    (hp : 1 < p) (hε : 0 < ε) (hs : IsOpen s) (hsc : IsPreconnected s)
    (hsep : ∀ y ∈ s, ε ≤ |y|) (ht : t ∈ s)
    (f : 𝓢(ℝ, ℂ)) (j : ℕ) :
    iteratedDeriv j (fun y => ∑' n : ℕ, f (p ^ n * y)) t =
      ∑' n : ℕ, expandingDerivTerm p f j n t := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hgeom := summable_geometric_of_lt_one (inv_nonneg.mpr hp0.le)
    (inv_lt_one_of_one_lt₀ hp)
  have h := iteratedDeriv_tsum_derivChain_on
    (a := expandingDerivTerm p f)
    (b := fun k n => (SchwartzMap.seminorm ℂ (k + 1) k f / ε ^ (k + 1)) *
      (p⁻¹) ^ n)
    hs hsc
    (fun k n y _ => hasDerivAt_expandingDerivTerm p f k n y)
    (fun k => hgeom.mul_left _)
    (fun k n y hy => norm_expandingDerivTerm_le hp hε (hsep y hy) f k n)
    j ht
  simpa only [expandingDerivTerm, pow_zero, iteratedDeriv_zero, one_smul] using h

/-- The actual expanding orbit sum has the expected derivatives at every
nonzero real point. No kernel or evenness hypothesis is used here. -/
theorem iteratedDeriv_tsum_expanding {p t : ℝ} (hp : 1 < p) (ht : t ≠ 0)
    (f : 𝓢(ℝ, ℂ)) (j : ℕ) :
    iteratedDeriv j (fun y => ∑' n : ℕ, f (p ^ n * y)) t =
      ∑' n : ℕ, expandingDerivTerm p f j n t := by
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · apply iteratedDeriv_tsum_expanding_on (ε := -t / 2) (s := Iio (t / 2)) hp
      (by linarith) isOpen_Iio isPreconnected_Iio ?_ (by change t < t / 2; linarith) f j
    intro y hy
    have hy' : y < t / 2 := hy
    linarith [neg_le_abs y]
  · apply iteratedDeriv_tsum_expanding_on (ε := t / 2) (s := Ioi (t / 2)) hp
      (by linarith) isOpen_Ioi isPreconnected_Ioi ?_ (by change t / 2 < t; linarith) f j
    intro y hy
    exact le_trans (le_of_lt hy) (le_abs_self y)

/-- Transfer the genuine local series derivative formula to the contracting
primitive using equality on a neighborhood avoiding zero. -/
theorem iteratedDeriv_contractingPrimitive_eq_tsum {p t : ℝ}
    (hp : 1 < p) (ht : t ≠ 0) (f : 𝓢(ℝ, ℂ))
    (hfe : Function.Even (f : ℝ → ℂ)) (hf0 : f 0 = 0)
    (hP : ∀ x : ℝ, periodization p f x = 0) (j : ℕ) :
    iteratedDeriv j (contractingPrimitive p f) t =
      ∑' n : ℕ, expandingDerivTerm p f j n t := by
  have heq : contractingPrimitive p f =ᶠ[𝓝 t]
      (fun y => ∑' n : ℕ, f (p ^ n * y)) := by
    filter_upwards [eventually_ne_nhds ht] with y hy
    exact contractingPrimitive_eq_expanding_of_periodization_zero hp hy f hfe hf0 hP
  rw [heq.iteratedDeriv_eq j]
  exact iteratedDeriv_tsum_expanding hp ht f j

#print axioms hasDerivAt_expandingDerivTerm
#print axioms iteratedDeriv_tsum_expanding_on
#print axioms iteratedDeriv_tsum_expanding
#print axioms iteratedDeriv_contractingPrimitive_eq_tsum

end MasulloLocal

/- Source module: MasulloLocal/KernelSchwartz.lean -/
/-!
# The actual Schwartz preimage in the periodization kernel

Smoothness at the origin comes from the contracting series; rapid decay at
infinity comes from the equal expanding series. Neither property is assumed
of the candidate. The final construction is a literal Mathlib Schwartz map.
-/

open scoped SchwartzMap FourierTransform ContDiff
open MeasureTheory Filter Topology

set_option autoImplicit false

noncomputable section

namespace MasulloLocal

/-- Exterior decay bounds for a smooth function suffice for the full Schwartz
decay condition: the remaining region is compact. -/
theorem schwartzDecay_of_exterior {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hext : ∀ k j : ℕ, ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| →
      |t| ^ k * ‖iteratedDeriv j g t‖ ≤ C) :
    ∀ k j : ℕ, ∃ C : ℝ, ∀ t : ℝ,
      ‖t‖ ^ k * ‖iteratedFDeriv ℝ j g t‖ ≤ C := by
  intro k j
  obtain ⟨Cext, hCext⟩ := hext k j
  have hc : Continuous (iteratedDeriv j g) :=
    ContDiff.continuous_iteratedDeriv j hg (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
  obtain ⟨Cint, hCint⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn
      hc.continuousOn
  refine ⟨max Cint Cext, fun t => ?_⟩
  rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases ht : |t| ≤ 1
  · calc
      |t| ^ k * ‖iteratedDeriv j g t‖ ≤ 1 * ‖iteratedDeriv j g t‖ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (abs_nonneg t) ht) (norm_nonneg _)
      _ ≤ Cint := by simpa only [one_mul] using hCint t (abs_le.mp ht)
      _ ≤ max Cint Cext := le_max_left _ _
  · exact (hCext t (le_of_lt (not_le.mp ht))).trans (le_max_right _ _)

/-- Vanishing of the actual bilateral orbit sum supplies all exterior decay
estimates for the contracting primitive. -/
theorem contractingPrimitive_schwartzDecay {p : ℝ} (hp : 1 < p)
    (f : 𝓢(ℝ, ℂ)) (hfe : Function.Even (f : ℝ → ℂ)) (hf0 : f 0 = 0)
    (hP : ∀ x : ℝ, periodization p f x = 0) :
    ∀ k j : ℕ, ∃ C : ℝ, ∀ t : ℝ,
      ‖t‖ ^ k * ‖iteratedFDeriv ℝ j (contractingPrimitive p f) t‖ ≤ C := by
  apply schwartzDecay_of_exterior (contDiff_contractingPrimitive hp f)
  intro k j
  refine ⟨∑' n : ℕ, SchwartzMap.seminorm ℂ (k + j + 1) j f * (p⁻¹) ^ n,
    fun t ht => ?_⟩
  have ht0 : t ≠ 0 := by
    intro h
    simp only [h, abs_zero] at ht
    linarith
  rw [iteratedDeriv_contractingPrimitive_eq_tsum hp ht0 f hfe hf0 hP j]
  exact weighted_norm_tsum_expandingDerivTerm_le hp ht f k j

/-- A literal Mathlib Schwartz map constructed from the convergent contracting
series. Smoothness and all Schwartz bounds are proved above. -/
def kernelPrimitive {p : ℝ} (hp : 1 < p)
    (f : 𝓢(ℝ, ℂ)) (hfe : Function.Even (f : ℝ → ℂ)) (hf0 : f 0 = 0)
    (hP : ∀ x : ℝ, periodization p f x = 0) : 𝓢(ℝ, ℂ) where
  toFun := contractingPrimitive p f
  smooth' := contDiff_contractingPrimitive hp f
  decay' := contractingPrimitive_schwartzDecay hp f hfe hf0 hP

@[simp] theorem kernelPrimitive_apply {p : ℝ} (hp : 1 < p)
    (f : 𝓢(ℝ, ℂ)) (hfe : Function.Even (f : ℝ → ℂ)) (hf0 : f 0 = 0)
    (hP : ∀ x : ℝ, periodization p f x = 0) (t : ℝ) :
    kernelPrimitive hp f hfe hf0 hP t = contractingPrimitive p f t := rfl

theorem kernelPrimitive_even {p : ℝ} (hp : 1 < p)
    (f : 𝓢(ℝ, ℂ)) (hfe : Function.Even (f : ℝ → ℂ)) (hf0 : f 0 = 0)
    (hP : ∀ x : ℝ, periodization p f x = 0) :
    Function.Even (kernelPrimitive hp f hfe hf0 hP : ℝ → ℂ) :=
  contractingPrimitive_even p f hfe

@[simp] theorem kernelPrimitive_zero {p : ℝ} (hp : 1 < p)
    (f : 𝓢(ℝ, ℂ)) (hfe : Function.Even (f : ℝ → ℂ)) (hf0 : f 0 = 0)
    (hP : ∀ x : ℝ, periodization p f x = 0) :
    kernelPrimitive hp f hfe hf0 hP 0 = 0 := contractingPrimitive_zero p f

/-- The constructed Schwartz function is an actual preimage of f. -/
theorem eulerDifference_kernelPrimitive {p : ℝ} (hp : 1 < p)
    (f : 𝓢(ℝ, ℂ)) (hfe : Function.Even (f : ℝ → ℂ)) (hf0 : f 0 = 0)
    (hP : ∀ x : ℝ, periodization p f x = 0) :
    eulerDifference p (ne_of_gt (lt_trans zero_lt_one hp))
      (kernelPrimitive hp f hfe hf0 hP) = f := by
  ext t
  exact contractingPrimitive_euler_eq_of_zero hp f hf0 t

#print axioms schwartzDecay_of_exterior
#print axioms contractingPrimitive_schwartzDecay
#print axioms kernelPrimitive
#print axioms eulerDifference_kernelPrimitive

end MasulloLocal

/- Source module: MasulloLocal/KernelBandAlgebra.lean -/
/-!
# Band and residue algebra for a genuine Schwartz preimage

This module only performs the final band/residue bookkeeping after a Schwartz
preimage has actually been constructed. It also bundles the already convergent
periodization as a pointwise complex-linear map, without asserting a `C∞` topology.
-/

open scoped SchwartzMap FourierTransform

set_option autoImplicit false

noncomputable section

namespace MasulloLocal

/-- For an expanding dilation, vanishing Fourier residue of its difference forces
vanishing Fourier residue of the original Schwartz function. -/
theorem fourier_zero_of_fourier_eulerDifference_zero {p : ℝ} (hp : 1 < p)
    (g : 𝓢(ℝ, ℂ))
    (hz : 𝓕 (eulerDifference p (ne_of_gt (lt_trans zero_lt_one hp)) g) 0 = 0) :
    𝓕 g 0 = 0 := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hd : 𝓕 g 0 - (p : ℂ)⁻¹ * 𝓕 g 0 = 0 := by
    calc
      𝓕 g 0 - (p : ℂ)⁻¹ * 𝓕 g 0
          = 𝓕 (eulerDifference p hp0.ne' g) (p * 0) := by
              simpa only [mul_zero] using (fourier_eulerDifference_mul hp0 g 0).symm
      _ = 0 := by simpa only [mul_zero] using hz
  by_contra hne
  have hc : (1 : ℂ) = (p : ℂ)⁻¹ :=
    mul_right_cancel₀ hne (by simpa only [one_mul] using sub_eq_zero.mp hd)
  have hp1 : (p : ℂ) = 1 := inv_eq_one.mp hc.symm
  have hp1r : p = 1 := by exact_mod_cast hp1
  exact (ne_of_gt hp) hp1r

/-- A genuine even Schwartz preimage with zero origin value belongs to the smaller
two-residue Fourier band. The Fourier residue and support are derived here. -/
theorem mem_E_of_eulerDifference_eq {p X : ℝ} (hp : 1 < p) (hX : 0 ≤ X)
    {f g : 𝓢(ℝ, ℂ)} (hf : f ∈ E (p * X))
    (hge : Function.Even (g : ℝ → ℂ)) (hg0 : g 0 = 0)
    (heq : eulerDifference p (ne_of_gt (lt_trans zero_lt_one hp)) g = f) :
    g ∈ E X := by
  refine ⟨hge, hg0, ?_, ?_⟩
  · apply fourier_zero_of_fourier_eulerDifference_zero hp g
    rw [heq]
    exact hf.2.2.1
  · apply inBand_of_eulerDifference hp hX g
    rw [heq]
    exact hf.2.2.2

/-- Actual periodization as a pointwise complex-linear map on the literal band core.
Continuity into a `C∞` topology is not included in this definition. -/
def periodizationBandLinearMap {p : ℝ} (hp : 1 < p) (X : ℝ) :
    E X →ₗ[ℂ] (ℝ → ℂ) where
  toFun f := periodization p (f : 𝓢(ℝ, ℂ))
  map_add' := by
    intro f g
    funext x
    change (∑' n : ℤ, ((f : 𝓢(ℝ, ℂ)) (p ^ n * Real.exp x) +
      (g : 𝓢(ℝ, ℂ)) (p ^ n * Real.exp x))) =
      (∑' n : ℤ, (f : 𝓢(ℝ, ℂ)) (p ^ n * Real.exp x)) +
      ∑' n : ℤ, (g : 𝓢(ℝ, ℂ)) (p ^ n * Real.exp x)
    exact (periodization_summable hp (f : 𝓢(ℝ, ℂ)) f.property.2.1 x).tsum_add
      (periodization_summable hp (g : 𝓢(ℝ, ℂ)) g.property.2.1 x)
  map_smul' := by
    intro c f
    funext x
    change (∑' n : ℤ, c • (f : 𝓢(ℝ, ℂ)) (p ^ n * Real.exp x)) =
      c • ∑' n : ℤ, (f : 𝓢(ℝ, ℂ)) (p ^ n * Real.exp x)
    exact Summable.tsum_const_smul c
      (periodization_summable hp (f : 𝓢(ℝ, ℂ)) f.property.2.1 x)

@[simp] theorem periodizationBandLinearMap_apply {p : ℝ} (hp : 1 < p)
    (X : ℝ) (f : E X) (x : ℝ) :
    periodizationBandLinearMap hp X f x = periodization p (f : 𝓢(ℝ, ℂ)) x := rfl

@[simp] theorem mem_ker_periodizationBandLinearMap {p : ℝ} (hp : 1 < p)
    (X : ℝ) (f : E X) :
    f ∈ LinearMap.ker (periodizationBandLinearMap hp X) ↔
      ∀ x : ℝ, periodization p (f : 𝓢(ℝ, ℂ)) x = 0 := by
  change (periodizationBandLinearMap hp X f = 0) ↔ _
  constructor
  · intro h x
    exact congrFun h x
  · intro h
    exact funext h

theorem range_eulerBandMap_le_ker_periodization {p X : ℝ}
    (hp : 1 < p) (hX : 0 ≤ X) :
    LinearMap.range (eulerBandMap hp hX).toLinearMap ≤
      LinearMap.ker (periodizationBandLinearMap hp (p * X)) := by
  rintro f ⟨g, rfl⟩
  apply (mem_ker_periodizationBandLinearMap hp (p * X) _).mpr
  exact periodization_eulerBandMap hp hX g

#print axioms mem_E_of_eulerDifference_eq
#print axioms periodizationBandLinearMap
#print axioms range_eulerBandMap_le_ker_periodization

end MasulloLocal

/- Source module: MasulloLocal/BandKernel.lean -/
/-!
# Exactness at the finite-bandwidth periodization kernel

The Schwartz preimage is the actual convergent contracting series, established
in `KernelSchwartz`. Its Fourier residue and the exact drop in Fourier bandwidth
are then derived from the dilation equation. The target map here is the actual
pointwise periodization; a continuous `C∞`-valued section is a separate theorem.
-/

open scoped SchwartzMap FourierTransform

set_option autoImplicit false

noncomputable section

namespace MasulloLocal

/-- Every element of the actual periodization kernel in `E_(pX)` has a preimage
in the smaller literal band `E_X`. -/
theorem exists_eulerBandMap_eq_of_periodization_zero {p X : ℝ}
    (hp : 1 < p) (hX : 0 ≤ X) (f : E (p * X))
    (hP : ∀ x : ℝ, periodization p (f : 𝓢(ℝ, ℂ)) x = 0) :
    ∃ g : E X, eulerBandMap hp hX g = f := by
  let g : 𝓢(ℝ, ℂ) := kernelPrimitive hp (f : 𝓢(ℝ, ℂ))
    f.property.1 f.property.2.1 hP
  have hge : Function.Even (g : ℝ → ℂ) := by
    intro t
    simp only [g, kernelPrimitive_apply]
    exact contractingPrimitive_even p (f : 𝓢(ℝ, ℂ)) f.property.1 t
  have hg0 : g 0 = 0 := by
    simp only [g, kernelPrimitive_apply, contractingPrimitive_zero]
  have heq : eulerDifference p (ne_of_gt (lt_trans zero_lt_one hp)) g =
      (f : 𝓢(ℝ, ℂ)) :=
    eulerDifference_kernelPrimitive hp (f : 𝓢(ℝ, ℂ)) f.property.1 f.property.2.1 hP
  have hgmem : g ∈ E X := mem_E_of_eulerDifference_eq hp hX f.property hge hg0 heq
  refine ⟨⟨g, hgmem⟩, ?_⟩
  apply Subtype.ext
  exact heq

/-- Pointwise vanishing of the convergent periodization is exactly membership in
the image of the actual first arrow. -/
theorem periodization_zero_iff_exists_eulerBandMap {p X : ℝ}
    (hp : 1 < p) (hX : 0 ≤ X) (f : E (p * X)) :
    (∀ x : ℝ, periodization p (f : 𝓢(ℝ, ℂ)) x = 0) ↔
      ∃ g : E X, eulerBandMap hp hX g = f := by
  constructor
  · exact exists_eulerBandMap_eq_of_periodization_zero hp hX f
  · rintro ⟨g, rfl⟩
    exact periodization_eulerBandMap hp hX g

/-- The preimage is unique, because expanding dilation differences are injective
on the genuine Schwartz space. -/
theorem periodization_zero_iff_existsUnique_eulerBandMap {p X : ℝ}
    (hp : 1 < p) (hX : 0 ≤ X) (f : E (p * X)) :
    (∀ x : ℝ, periodization p (f : 𝓢(ℝ, ℂ)) x = 0) ↔
      ∃! g : E X, eulerBandMap hp hX g = f := by
  constructor
  · intro hP
    obtain ⟨g, hg⟩ := exists_eulerBandMap_eq_of_periodization_zero hp hX f hP
    refine ⟨g, hg, ?_⟩
    intro g' hg'
    exact eulerBandMap_injective hp hX (hg'.trans hg.symm)
  · rintro ⟨g, hg, _⟩
    exact (periodization_zero_iff_exists_eulerBandMap hp hX f).mpr ⟨g, hg⟩

/-- Exactness as an equality of submodules for the actual pointwise periodization. -/
theorem range_eulerBandMap_eq_ker_periodization {p X : ℝ}
    (hp : 1 < p) (hX : 0 ≤ X) :
    LinearMap.range (eulerBandMap hp hX).toLinearMap =
      LinearMap.ker (periodizationBandLinearMap hp (p * X)) := by
  apply le_antisymm (range_eulerBandMap_le_ker_periodization hp hX)
  intro f hf
  exact exists_eulerBandMap_eq_of_periodization_zero hp hX f
    ((mem_ker_periodizationBandLinearMap hp (p * X) f).mp hf)

#print axioms exists_eulerBandMap_eq_of_periodization_zero
#print axioms periodization_zero_iff_existsUnique_eulerBandMap
#print axioms range_eulerBandMap_eq_ker_periodization

end MasulloLocal

/- Source module: Publication/KernelExactnessStatement.lean -/
/-! The public proposition uses only upstream Mathlib definitions. -/

open scoped SchwartzMap FourierTransform

set_option autoImplicit false

noncomputable section

def KernelExactnessStatement : Prop :=
  ∀ (p X : ℝ), 1 < p → 0 ≤ X → ∀ f : 𝓢(ℝ, ℂ),
    Function.Even (f : ℝ → ℂ) → f 0 = 0 → 𝓕 f 0 = 0 →
    Function.support (⇑(𝓕 f : 𝓢(ℝ, ℂ))) ⊆ Set.Icc (-(p * X)) (p * X) →
    ((∀ x : ℝ, (∑' n : ℤ, f (p ^ n * Real.exp x)) = 0) ↔
      ∃! g : 𝓢(ℝ, ℂ),
        Function.Even (g : ℝ → ℂ) ∧ g 0 = 0 ∧ 𝓕 g 0 = 0 ∧
        Function.support (⇑(𝓕 g : 𝓢(ℝ, ℂ))) ⊆ Set.Icc (-X) X ∧
        ∀ t : ℝ, g t - g (p * t) = f t)

/- Source module: Publication/KernelExactnessSolution.lean -/
open scoped SchwartzMap FourierTransform
open MasulloLocal

set_option autoImplicit false

noncomputable section

/-- The checked result inhabits the exact public proposition, independently
written with literal Schwartz, Fourier-support, and orbit-sum conditions. -/
theorem kernelExactnessSolution : KernelExactnessStatement := by
  intro p X hp hX f hfe hf0 hFf0 hfB
  let fb : E (p * X) := ⟨f, hfe, hf0, hFf0, hfB⟩
  constructor
  · intro hP
    obtain ⟨g, hg, hu⟩ :=
      (periodization_zero_iff_existsUnique_eulerBandMap hp hX fb).mp hP
    refine ⟨(g : 𝓢(ℝ, ℂ)),
      ⟨g.property.1, g.property.2.1, g.property.2.2.1, g.property.2.2.2, ?_⟩, ?_⟩
    · intro t
      exact congrArg (fun z : E (p * X) => (z : 𝓢(ℝ, ℂ)) t) hg
    · intro g' hg'
      let gb' : E X := ⟨g', hg'.1, hg'.2.1, hg'.2.2.1, hg'.2.2.2.1⟩
      have hmap : eulerBandMap hp hX gb' = fb := by
        apply Subtype.ext
        ext t
        exact hg'.2.2.2.2 t
      exact congrArg (fun z : E X => (z : 𝓢(ℝ, ℂ))) (hu gb' hmap)
  · rintro ⟨g, hg, _⟩
    have heq : eulerDifference p (ne_of_gt (lt_trans zero_lt_one hp)) g = f := by
      ext t
      exact hg.2.2.2.2 t
    intro x
    change periodization p f x = 0
    rw [← heq, periodization_eulerDifference hp, hg.2.1]

#print axioms kernelExactnessSolution

theorem solution :
  ∀ (p X : ℝ), 1 < p → 0 ≤ X → ∀ f : 𝓢(ℝ, ℂ),
    Function.Even (f : ℝ → ℂ) → f 0 = 0 → 𝓕 f 0 = 0 →
    Function.support (⇑(𝓕 f : 𝓢(ℝ, ℂ))) ⊆ Set.Icc (-(p * X)) (p * X) →
    ((∀ x : ℝ, (∑' n : ℤ, f (p ^ n * Real.exp x)) = 0) ↔
      ∃! g : 𝓢(ℝ, ℂ),
        Function.Even (g : ℝ → ℂ) ∧ g 0 = 0 ∧ 𝓕 g 0 = 0 ∧
        Function.support (⇑(𝓕 g : 𝓢(ℝ, ℂ))) ⊆ Set.Icc (-X) X ∧
        ∀ t : ℝ, g t - g (p * t) = f t) := kernelExactnessSolution
#print axioms solution
