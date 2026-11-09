-- Prove2me | solution 1 for OAI.SharpPlanar.direct_spectral_bound_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T08:41:27.76019+00:00
-- url     : https://prove2.me/submissions/3f6cb9ee-1c56-4709-9881-e719e7a60dc0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098G1642
import Definitions.Def_OAIQ098G1643
import Definitions.Def_OAIQ098G1675
import Theorems.Thm_OAI_SharpPlanar_Pmoment_norm_bound_g
import Theorems.Thm_OAI_SharpPlanar_densityCap_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_directDensity_series_g
import Theorems.Thm_OAI_SharpPlanar_piece_density_bound_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_DirectBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Direct spectral estimates

The norm of the direct spectral kernel gives derivative bounds for cardinal functions.
-/

namespace SharpPlanar
open MeasureTheory Set IntegerBasis
open scoped BigOperators
lemma directKernel_norm (ell : ℕ) (s t : ℝ) :
    ‖directKernel ell s t‖=(Real.pi*|t|)^ell := by
  unfold directKernel
  rw [norm_mul,norm_pow,norm_mul,norm_mul,Complex.norm_I,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos,one_mul,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_exp]
  have he : (Complex.I*Real.pi*(t:ℂ)*s).re=0 := by simp
  rw [he,Real.exp_zero,mul_one]
lemma direct_piece_bound (p : CardinalData) (j : Fin 6) (ell : ℕ) (s : ℝ) :
    ‖∫ t in (j.val:ℝ)/6..((j.val:ℝ)+1)/6, density p j.val t*directKernel ell s t‖ ≤
      (|p.c₀|+|p.d₀|+‖p.x‖)*densityCap j/6*(Real.pi*((j.val:ℝ)+1)/6)^ell := by
  have hlen : ((j.val:ℝ)+1)/6-(j.val:ℝ)/6=1/6 := by ring
  have hlu : (j.val:ℝ)/6 ≤ ((j.val:ℝ)+1)/6 := by linarith
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (j.val:ℝ)/6) (b := ((j.val:ℝ)+1)/6)
    (C := (|p.c₀|+|p.d₀|+‖p.x‖)*densityCap j*(Real.pi*((j.val:ℝ)+1)/6)^ell)
    (f := fun t => density p j.val t*directKernel ell s t) (fun t ht => by
      have ht' : t ∈ Set.Icc ((j.val:ℝ)/6) (((j.val:ℝ)+1)/6) :=
        uIcc_of_le hlu ▸ Set.uIoc_subset_uIcc ht
      have ht0 : 0≤t := (by positivity : (0:ℝ)≤(j.val:ℝ)/6).trans ht'.1
      rw [norm_mul,directKernel_norm,abs_of_nonneg ht0]
      have hd:=piece_density_bound_g p j ht'
      have hk : (Real.pi*t)^ell≤(Real.pi*((j.val:ℝ)+1)/6)^ell := by
        apply pow_le_pow_left₀ (mul_nonneg Real.pi_pos.le ht0)
        nlinarith [Real.pi_pos,ht'.2]
      have h:=mul_le_mul hd hk (by positivity : 0≤(Real.pi*t)^ell)
        (mul_nonneg (densityCap_nonneg_g j) (by positivity))
      simpa only [mul_comm (densityCap j) (|p.c₀|+|p.d₀|+‖p.x‖)] using h)
  rw [hlen,abs_of_nonneg (by norm_num : (0:ℝ)≤1/6)] at hh
  convert hh using 1 <;> first | rfl | ring
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Envelopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spectral derivative bounds

Monotone spectral envelopes bound the cardinal functions and their Fourier kernels.
The estimates follow *A sharp Fourier certificate for planar circle packing*
(OpenAI, 2026).
-/

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
lemma direct_spectral_bound_g_oai (p : CardinalData) (ell : ℕ) (s : ℝ) :
    |cardinalSeries p ell s| ≤ 
      |p.C| *25*Real.pi^ell+(|p.c₀|+|p.d₀|+‖p.x‖)*directEnvelope ell := by
  have he:=directDensity_series_g p ell s
  have he' : cardinalSeries p ell s=p.C*Pmoment ell s+
    (∑ j ∈ Finset.range 6,∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      density p j t*directKernel ell s t).re := by
    rw [he]; unfold cardinalSeries; ring
  rw [he']
  apply (abs_add_le _ _).trans
  apply add_le_add
  · rw [abs_mul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (Pmoment_norm_bound_g ell s) (abs_nonneg _)
  · apply (Complex.abs_re_le_norm _).trans
    rw [← Fin.sum_univ_eq_sum_range]
    apply (norm_sum_le _ _).trans
    unfold directEnvelope
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro j _
    simpa only [mul_div_assoc,mul_assoc] using direct_piece_bound p j ell s
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.direct_spectral_bound_g_oai := @OAI.SharpPlanar.direct_spectral_bound_g_oai
