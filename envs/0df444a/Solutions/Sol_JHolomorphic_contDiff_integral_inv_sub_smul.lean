-- Prove2me | solution 1 for JHolomorphic.contDiff_integral_inv_sub_smul
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T09:18:36.76+00:00
-- url     : https://prove2.me/submissions/ec2bcd1d-0420-4a74-a2fd-e869999291f0

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Theorems.Thm_Complex_integral_inv_sub_mul_dbar_eq_neg_pi_mul



namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal

/-- `w ↦ w⁻¹` restricted to a disc lies in `L^q` for `1 ≤ q < 2`. -/
theorem memLp_indicator_ball_inv {q : ℝ} (hq1 : 1 ≤ q) (hq2 : q < 2) (r : ℝ) :
    MemLp ((ball (0 : ℂ) r).indicator fun w : ℂ => w⁻¹) (ENNReal.ofReal q) volume := by
  have hq0 : 0 < q := by linarith
  rw [memLp_indicator_iff_restrict measurableSet_ball]
  have hmeas : AEStronglyMeasurable (fun w : ℂ => w⁻¹) (volume.restrict (ball 0 r)) :=
    (measurable_inv.aestronglyMeasurable)
  rw [← integrable_norm_rpow_iff hmeas (by simpa using hq0) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq0.le]
  show IntegrableOn (fun w : ℂ => ‖w⁻¹‖ ^ q) (ball 0 r) volume
  simp_rw [norm_inv]
  rw [integrableOn_fun_norm_addHaar volume (f := fun y : ℝ => y⁻¹ ^ q), Complex.finrank_real_complex]
  rcases le_or_gt r 0 with hr | hr
  · rw [Ioo_eq_empty (by linarith)]; exact integrableOn_empty
  refine ((intervalIntegral.integrableOn_Ioo_rpow_iff (s := 1 - q) hr).2 (by linarith)).congr_fun
    (fun y hy => ?_) measurableSet_Ioo
  have hy0 : 0 < y := hy.1
  simp only [smul_eq_mul, pow_one]
  rw [Real.inv_rpow hy0.le, ← Real.rpow_neg hy0.le, Real.rpow_sub hy0, Real.rpow_one,
    Real.rpow_neg hy0.le, div_eq_mul_inv]
  norm_num

set_option maxHeartbeats 400000 in
/-- Sup bound for the Cauchy kernel against compactly supported `L^p` data, `p > 2`. -/
theorem norm_integral_inv_sub_smul_le_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p R : ℝ) (hp : 2 < p) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℂ → E, MemLp g (ENNReal.ofReal p) volume →
      Function.support g ⊆ ball 0 R → ∀ z ∈ ball (0 : ℂ) R,
        Integrable (fun ζ => (z - ζ)⁻¹ • g ζ) ∧
        ‖∫ ζ, (z - ζ)⁻¹ • g ζ‖ ≤ C * (eLpNorm g (ENNReal.ofReal p) volume).toReal := by
  set q : ℝ := p / (p - 1) with hqdef
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent (by linarith)
  have hq1 : 1 ≤ q := by rw [hqdef, le_div_iff₀ (by linarith)]; linarith
  have hq2 : q < 2 := by
    rw [hqdef, div_lt_iff₀ (by linarith)]; linarith
  haveI : ENNReal.HolderTriple (ENNReal.ofReal q) (ENNReal.ofReal p) 1 :=
    ⟨by rw [inv_one, add_comm]; exact hpq.inv_add_inv_ennreal⟩
  obtain ⟨k0, hk0def⟩ : ∃ k0 : ℂ → ℂ, k0 = (ball (0 : ℂ) (2 * R)).indicator fun w : ℂ => w⁻¹ :=
    ⟨_, rfl⟩
  have hk0 : MemLp k0 (ENNReal.ofReal q) volume := hk0def ▸ memLp_indicator_ball_inv hq1 hq2 _
  refine ⟨(eLpNorm k0 (ENNReal.ofReal q) volume).toReal, ENNReal.toReal_nonneg,
    fun g hg hsupp z hz => ?_⟩
  have hmp : MeasurePreserving (fun ζ : ℂ => z - ζ) volume volume :=
    Measure.measurePreserving_sub_left volume z
  obtain ⟨k1, hk1def⟩ : ∃ k1 : ℂ → ℂ, k1 = fun ζ => k0 (z - ζ) := ⟨_, rfl⟩
  have hk1 : MemLp k1 (ENNReal.ofReal q) volume := hk1def ▸ hk0.comp_measurePreserving hmp
  have hk1n : eLpNorm k1 (ENNReal.ofReal q) volume = eLpNorm k0 (ENNReal.ofReal q) volume :=
    hk1def ▸ eLpNorm_comp_measurePreserving hk0.1 hmp
  have hF : (fun ζ => (z - ζ)⁻¹ • g ζ) = k1 • g := by
    funext ζ
    by_cases hζ : ζ ∈ Function.support g
    · have hζR := mem_ball_zero_iff.1 (hsupp hζ)
      have hzR := mem_ball_zero_iff.1 hz
      have : z - ζ ∈ ball (0 : ℂ) (2 * R) := by
        rw [mem_ball_zero_iff]
        calc ‖z - ζ‖ ≤ ‖z‖ + ‖ζ‖ := norm_sub_le _ _
          _ < 2 * R := by linarith
      rw [hk1def]; show _ = k0 (z - ζ) • g ζ
      rw [hk0def, indicator_of_mem this]
    · rw [Function.notMem_support] at hζ
      simp [hζ]
  have hmem : MemLp (k1 • g) 1 volume := hg.smul hk1
  refine ⟨by rw [hF]; exact memLp_one_iff_integrable.1 hmem, ?_⟩
  have hle : ‖∫ ζ, (z - ζ)⁻¹ • g ζ‖ₑ ≤
      eLpNorm k0 (ENNReal.ofReal q) volume * eLpNorm g (ENNReal.ofReal p) volume := by
    calc ‖∫ ζ, (z - ζ)⁻¹ • g ζ‖ₑ ≤ ∫⁻ ζ, ‖(z - ζ)⁻¹ • g ζ‖ₑ := enorm_integral_le_lintegral_enorm _
      _ = eLpNorm (k1 • g) 1 volume := by rw [eLpNorm_one_eq_lintegral_enorm, ← hF]
      _ ≤ eLpNorm k1 (ENNReal.ofReal q) volume * eLpNorm g (ENNReal.ofReal p) volume :=
          eLpNorm_smul_le_mul_eLpNorm hg.1 hk1.1
      _ = _ := by rw [hk1n]
  have hfin : eLpNorm k0 (ENNReal.ofReal q) volume * eLpNorm g (ENNReal.ofReal p) volume ≠ ⊤ :=
    ENNReal.mul_ne_top hk0.eLpNorm_ne_top hg.eLpNorm_ne_top
  rw [← ENNReal.toReal_mul, ← toReal_enorm]
  exact ENNReal.toReal_mono hfin hle

end JHolomorphic

namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Convolution

theorem locallyIntegrable_inv_complex : LocallyIntegrable (fun t : ℂ => t⁻¹) volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨r, hr⟩ := hk.isBounded.subset_ball 0
  have h1 := memLp_indicator_ball_inv (q := 1) le_rfl (by norm_num) r
  rw [ENNReal.ofReal_one, memLp_one_iff_integrable,
    integrable_indicator_iff measurableSet_ball] at h1
  exact h1.mono_set hr

/-- the Cauchy-type integral as a convolution -/
theorem integral_inv_sub_smul_eq_convolution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (h : ℂ → E) :
    (fun z => ∫ ζ, (z - ζ)⁻¹ • h ζ) =
      (fun t : ℂ => t⁻¹) ⋆[(ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] E →L[ℝ] E), volume] h := by
  funext z
  rw [convolution_def, ← integral_sub_left_eq_self _ volume z]
  congr 1
  funext t
  simp

theorem integral_inv_sub_smul_dbar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (h : ℂ → E) (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport h) (z : ℂ)
    (hint : Integrable (fun ζ => (z - ζ)⁻¹ • (fderiv ℝ h ζ 1 + Complex.I • fderiv ℝ h ζ Complex.I))) :
    ∫ ζ, (z - ζ)⁻¹ • (fderiv ℝ h ζ 1 + Complex.I • fderiv ℝ h ζ Complex.I) =
      (2 * Real.pi : ℂ) • h z := by
  rw [NormedSpace.eq_iff_forall_dual_eq ℂ]
  intro ℓ
  have hℓh : ContDiff ℝ 1 (fun x => ℓ (h x)) := (ℓ.restrictScalars ℝ).contDiff.comp hh
  have hℓc : HasCompactSupport (fun x => ℓ (h x)) := hc.comp_left (map_zero ℓ)
  have hder : ∀ ζ v, fderiv ℝ (fun x => ℓ (h x)) ζ v = ℓ (fderiv ℝ h ζ v) := by
    intro ζ v
    have hd : HasFDerivAt (fun x => ℓ (h x)) ((ℓ.restrictScalars ℝ).comp (fderiv ℝ h ζ)) ζ :=
      (ℓ.restrictScalars ℝ).hasFDerivAt.comp ζ ((hh.differentiable one_ne_zero) ζ).hasFDerivAt
    rw [hd.fderiv]
    rfl
  have hP := Complex.integral_inv_sub_mul_dbar_eq_neg_pi_mul z _ hℓh hℓc
  simp_rw [hder] at hP
  rw [← ContinuousLinearMap.integral_comp_comm ℓ hint, map_smul, smul_eq_mul]
  have hrw : ∀ ζ, ℓ ((z - ζ)⁻¹ • (fderiv ℝ h ζ 1 + Complex.I • fderiv ℝ h ζ Complex.I)) =
      (-2 : ℂ) * ((ζ - z)⁻¹ * ((ℓ (fderiv ℝ h ζ 1) + Complex.I * ℓ (fderiv ℝ h ζ Complex.I)) / 2)) := by
    intro ζ
    rw [map_smul, map_add, map_smul, smul_eq_mul, smul_eq_mul]
    rcases eq_or_ne ζ z with rfl | hne
    · simp
    · have : z - ζ = -(ζ - z) := by ring
      rw [this, inv_neg]
      ring
  simp_rw [hrw]
  rw [integral_const_mul, hP]
  ring

theorem integrable_inv_sub_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g : ℂ → E} (hg : Continuous g) (hgc : HasCompactSupport g) (z : ℂ) :
    Integrable (fun ζ => (z - ζ)⁻¹ • g ζ) := by
  have h1 := hgc.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] E →L[ℝ] E)
    locallyIntegrable_inv_complex hg z
  have h2 := Integrable.comp_sub_left h1 z
  simpa using h2

/-- Smooth case of the Cauchy transform. -/
theorem contDiff_integral_inv_sub_smul_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (h : ℂ → E) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    ContDiff ℝ ∞ (fun z => ∫ ζ, (z - ζ)⁻¹ • h ζ) ∧
      ∀ z, fderiv ℝ (fun z => ∫ ζ, (z - ζ)⁻¹ • h ζ) z 1 +
          Complex.I • fderiv ℝ (fun z => ∫ ζ, (z - ζ)⁻¹ • h ζ) z Complex.I =
        (2 * Real.pi : ℂ) • h z := by
  obtain ⟨L, hL⟩ : ∃ L : ℂ →L[ℝ] E →L[ℝ] E, L = ContinuousLinearMap.lsmul ℝ ℂ := ⟨_, rfl⟩
  have hconv : ∀ g : ℂ → E, (fun z => ∫ ζ, (z - ζ)⁻¹ • g ζ) =
      (fun t : ℂ => t⁻¹) ⋆[L, volume] g := fun g => hL ▸ integral_inv_sub_smul_eq_convolution g
  have hK := locallyIntegrable_inv_complex
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by exact_mod_cast le_top)
  rw [hconv h]
  refine ⟨hc.contDiff_convolution_right L hK hh, fun z => ?_⟩
  have hD : ∀ v, fderiv ℝ ((fun t : ℂ => t⁻¹) ⋆[L, volume] h) z v =
      ∫ ζ, (z - ζ)⁻¹ • fderiv ℝ h ζ v := by
    intro v
    rw [(hc.hasFDerivAt_convolution_right L hK hh1 z).fderiv,
      convolution_precompR_apply L hK (hc.fderiv ℝ) (hh1.continuous_fderiv one_ne_zero) z v,
      ← hconv]
  rw [hD, hD]
  have hI : ∀ v, Integrable (fun ζ => (z - ζ)⁻¹ • fderiv ℝ h ζ v) := fun v =>
    integrable_inv_sub_smul ((hh1.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (hc.fderiv_apply ℝ v) z
  have hI' : Integrable (fun ζ => Complex.I • ((z - ζ)⁻¹ • fderiv ℝ h ζ Complex.I)) :=
    (hI Complex.I).smul Complex.I
  rw [← integral_smul, ← integral_add (hI 1) hI']
  have hrw : ∀ ζ, (z - ζ)⁻¹ • fderiv ℝ h ζ 1 + Complex.I • ((z - ζ)⁻¹ • fderiv ℝ h ζ Complex.I) =
      (z - ζ)⁻¹ • (fderiv ℝ h ζ 1 + Complex.I • fderiv ℝ h ζ Complex.I) := by
    intro ζ; rw [smul_add, smul_comm]
  simp_rw [hrw]
  exact integral_inv_sub_smul_dbar h hh1 hc z (by
    have := (hI 1).add hI'
    refine this.congr (Eventually.of_forall fun ζ => ?_)
    exact hrw ζ)

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (h : ℂ → E) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    ContDiff ℝ ∞ (fun z => ∫ ζ, (z - ζ)⁻¹ • h ζ) ∧
      ∀ z, fderiv ℝ (fun z => ∫ ζ, (z - ζ)⁻¹ • h ζ) z 1 +
          Complex.I • fderiv ℝ (fun z => ∫ ζ, (z - ζ)⁻¹ • h ζ) z Complex.I =
        (2 * Real.pi : ℂ) • h z :=
  contDiff_integral_inv_sub_smul_aux h hh hc
