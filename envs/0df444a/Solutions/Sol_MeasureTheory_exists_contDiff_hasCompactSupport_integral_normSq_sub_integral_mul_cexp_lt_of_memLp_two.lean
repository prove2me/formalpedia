-- Prove2me | solution 1 for MeasureTheory.exists_contDiff_hasCompactSupport_integral_normSq_sub_integral_mul_cexp_lt_of_memLp_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/bb4a0062-6111-55c6-a0b2-83faa1b8ab49

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_contDiff_hasCompactSupport_integral_normSq_sub_integral_mul_cexp_lt_of_memLp_two

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate ContDiff

open scoped FourierTransform

namespace FourierDensityAux

noncomputable def dil : ℝ := -(2 * Real.pi)⁻¹

theorem dil_ne_zero : dil ≠ 0 := by
  unfold dil
  exact neg_ne_zero.2 (inv_ne_zero (by positivity))

theorem abs_dil_inv : |dil⁻¹| = 2 * Real.pi := by
  unfold dil
  rw [inv_neg, inv_inv, abs_neg, abs_of_pos (by positivity)]

theorem fourier_apply_dil_mul (h : ℝ → ℂ) (t : ℝ) :
    𝓕 h (dil * t) = ∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)) := by
  rw [Real.fourier_real_eq]
  congr 1
  funext v
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm]
  congr 2
  unfold dil
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  push_cast
  field_simp

theorem memLp_comp_mul {G : ℝ → ℂ} (hG : MemLp G 2 volume) {b : ℝ} (hb : b ≠ 0) :
    MemLp (fun y : ℝ => G (b * y)) 2 volume := by
  have h1 : MemLp G 2 (Measure.map (fun y : ℝ => b * y) volume) := by
    rw [Real.map_volume_mul_left hb]
    exact hG.smul_measure ENNReal.ofReal_ne_top
  exact h1.comp_of_map (measurable_id.const_mul b).aemeasurable

theorem toReal_eLpNorm_eq_sqrt {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    (eLpNorm f 2 volume).toReal = Real.sqrt (∫ x, ‖f x‖ ^ 2) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun a => Real.rpow_nonneg (norm_nonneg _) _) _),
    Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, one_div]

theorem integral_norm_sq_eq_sq {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    (∫ x, ‖f x‖ ^ 2) = (eLpNorm f 2 volume).toReal ^ 2 := by
  rw [toReal_eLpNorm_eq_sqrt hf, Real.sq_sqrt (integral_nonneg fun x => by positivity)]

theorem norm_sub_eq_toReal {u v : Lp ℂ 2 (volume : Measure ℝ)} {f g : ℝ → ℂ}
    (hu : (u : ℝ → ℂ) =ᵐ[volume] f) (hv : (v : ℝ → ℂ) =ᵐ[volume] g) :
    ‖u - v‖ = (eLpNorm (f - g) 2 volume).toReal := by
  rw [Lp.norm_def]
  congr 1
  refine eLpNorm_congr_ae ?_
  filter_upwards [Lp.coeFn_sub u v, hu, hv] with x h1 h2 h3
  rw [h1, Pi.sub_apply, Pi.sub_apply, h2, h3]

end FourierDensityAux

open FourierDensityAux in

theorem solution
    (G : ℝ → ℂ) (_hG : MemLp G 2) (ε : ℝ) (_hε : 0 < ε) :
    ∃ h : ℝ → ℂ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧
      MemLp (fun t : ℝ => ∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) 2 ∧
      ∫ t : ℝ, ‖G t - ∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))‖ ^ 2 < ε := by

  have hdi : dil⁻¹ ≠ 0 := inv_ne_zero dil_ne_zero
  have hGt : MemLp (fun y : ℝ => G (dil⁻¹ * y)) 2 volume := memLp_comp_mul _hG hdi
  obtain ⟨g, hg⟩ : ∃ g : Lp ℂ 2 (volume : Measure ℝ), g = hGt.toLp (fun y : ℝ => G (dil⁻¹ * y)) :=
    ⟨_, rfl⟩
  have hgcoe : (g : ℝ → ℂ) =ᵐ[volume] (fun y : ℝ => G (dil⁻¹ * y)) := by
    rw [hg]
    exact MemLp.coeFn_toLp hGt

  obtain ⟨f, hf⟩ : ∃ f : Lp ℂ 2 (volume : Measure ℝ), f = 𝓕⁻ g := ⟨_, rfl⟩
  have hF : MemLp (f : ℝ → ℂ) 2 volume := Lp.memLp f
  obtain ⟨δ, hδpos, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ 2 * Real.pi * δ ^ 2 < ε := by
    refine ⟨Real.sqrt (ε / (4 * Real.pi)), Real.sqrt_pos.2 (by positivity), ?_⟩
    rw [Real.sq_sqrt (by positivity)]
    have : 2 * Real.pi * (ε / (4 * Real.pi)) = ε / 2 := by
      field_simp
      ring
    rw [this]
    linarith
  obtain ⟨h, hc, hh, happrox⟩ := hF.exist_eLpNorm_sub_le ENNReal.ofNat_ne_top one_le_two hδpos
  obtain ⟨S, hSh⟩ : ∃ S : SchwartzMap ℝ ℂ, (S : ℝ → ℂ) = h := ⟨hc.toSchwartzMap hh, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : SchwartzMap ℝ ℂ, T = 𝓕 S := ⟨_, rfl⟩
  have hTcoe : (T : ℝ → ℂ) = 𝓕 h := by rw [hT, SchwartzMap.fourier_coe, hSh]

  have hFI : (fun t : ℝ => ∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)))
      = fun t : ℝ => T (dil * t) := by
    funext t
    rw [hTcoe, fourier_apply_dil_mul]
  refine ⟨h, hh, hc, ?_, ?_⟩
  · rw [hFI]
    exact memLp_comp_mul (T.memLp 2 volume) dil_ne_zero

  have h1 : ‖S.toLp 2 volume - f‖ ≤ δ := by
    rw [norm_sub_eq_toReal ((S.coeFn_toLp 2 volume).trans (Filter.EventuallyEq.of_eq hSh))
      (Filter.EventuallyEq.rfl (f := (f : ℝ → ℂ))), eLpNorm_sub_comm]
    exact ENNReal.toReal_le_of_le_ofReal hδpos.le happrox

  have h2 : ‖T.toLp 2 volume - g‖ ≤ δ := by
    have e1 : T.toLp 2 volume = 𝓕 (S.toLp 2 volume) := by
      rw [hT]
      exact (SchwartzMap.toLp_fourier_eq S).symm
    have e2 : g = 𝓕 f := by rw [hf, FourierInvPair.fourier_fourierInv_eq]
    have e3 : 𝓕 (S.toLp 2 volume) - 𝓕 f = 𝓕 (S.toLp 2 volume - f) :=
      ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).map_sub (S.toLp 2 volume) f).symm
    rw [e1, e2, e3, Lp.norm_fourier_eq]
    exact h1

  have hD : MemLp ((fun y : ℝ => G (dil⁻¹ * y)) - (T : ℝ → ℂ)) 2 volume := hGt.sub (T.memLp 2 volume)
  have h3 : (∫ y : ℝ, ‖((fun y : ℝ => G (dil⁻¹ * y)) - (T : ℝ → ℂ)) y‖ ^ 2) ≤ δ ^ 2 := by
    rw [integral_norm_sq_eq_sq hD, ← norm_sub_eq_toReal hgcoe (T.coeFn_toLp 2 volume), norm_sub_rev]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 2

  have h4 : (∫ t : ℝ, ‖G t - ∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))‖ ^ 2)
      = |dil⁻¹| * ∫ y : ℝ, ‖((fun y : ℝ => G (dil⁻¹ * y)) - (T : ℝ → ℂ)) y‖ ^ 2 := by
    have e5 : ∀ t : ℝ, ‖G t - ∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))‖ ^ 2
        = (fun y : ℝ => ‖((fun y : ℝ => G (dil⁻¹ * y)) - (T : ℝ → ℂ)) y‖ ^ 2) (dil * t) := by
      intro t
      simp only [Pi.sub_apply]
      rw [← mul_assoc, inv_mul_cancel₀ dil_ne_zero, one_mul, ← fourier_apply_dil_mul h t, hTcoe]
    simp_rw [e5]
    rw [Measure.integral_comp_mul_left (fun y : ℝ => ‖((fun y : ℝ => G (dil⁻¹ * y)) - (T : ℝ → ℂ)) y‖ ^ 2) dil,
      smul_eq_mul]
  rw [h4, abs_dil_inv]
  exact (mul_le_mul_of_nonneg_left h3 (by positivity)).trans_lt hδε

end S_MeasureTheory_exists_contDiff_hasCompactSupport_integral_normSq_sub_integral_mul_cexp_lt_of_memLp_two
end P2MW
export P2MW.S_MeasureTheory_exists_contDiff_hasCompactSupport_integral_normSq_sub_integral_mul_cexp_lt_of_memLp_two (solution)
