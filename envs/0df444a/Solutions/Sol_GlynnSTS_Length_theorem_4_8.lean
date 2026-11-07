-- Prove2me | solution 1 for GlynnSTS.Length.theorem_4_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T10:42:28.095872+00:00
-- url     : https://prove2.me/submissions/8a98e0be-f78c-425c-9aff-3e46230d5d24

import Mathlib
import Definitions.Def_GlynnSTS_Length_Setting
import Theorems.Thm_GlynnSTS_Length_display_2_9

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace GlynnSTSThm48

noncomputable abbrev Φ : ℝ → ℝ := cdf (gaussianReal 0 1)

theorem Phi_eq_integral (y : ℝ) : Φ y = ∫ x in Set.Iic y, gaussianPDFReal 0 1 x := by
  simp only [Φ]
  rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero,
    ENNReal.toReal_ofReal]
  exact setIntegral_nonneg measurableSet_Iic (fun x _ => gaussianPDFReal_nonneg _ _ x)

theorem Phi_eq (y : ℝ) : Φ y = Φ 0 + ∫ x in (0:ℝ)..y, gaussianPDFReal 0 1 x := by
  rw [Phi_eq_integral, Phi_eq_integral, ← intervalIntegral.integral_Iic_sub_Iic]
  · ring
  · exact (integrable_gaussianPDFReal _ _).integrableOn
  · exact (integrable_gaussianPDFReal _ _).integrableOn

theorem continuous_pdf : Continuous (gaussianPDFReal 0 1) := by
  rw [gaussianPDFReal_def]; fun_prop

theorem hasDerivAt_Phi (y : ℝ) : HasDerivAt Φ (gaussianPDFReal 0 1 y) y := by
  have h := intervalIntegral.integral_hasDerivAt_right (a := 0) (b := y)
    (continuous_pdf.intervalIntegrable _ _)
    (continuous_pdf.stronglyMeasurableAtFilter _ _) continuous_pdf.continuousAt
  have hfun : Φ = fun u => Φ 0 + ∫ x in (0:ℝ)..u, gaussianPDFReal 0 1 x := funext Phi_eq
  rw [hfun]
  exact h.const_add _

theorem continuous_Phi : Continuous Φ :=
  continuous_iff_continuousAt.2 (fun y => (hasDerivAt_Phi y).continuousAt)

theorem strictMono_Phi : StrictMono Φ := by
  intro a b hab
  have h1 : (gaussianReal 0 1) (Set.Ioc a b) = ENNReal.ofReal (Φ b - Φ a) := by
    simp only [Φ]
    rw [← StieltjesFunction.measure_Ioc, measure_cdf]
  have h2 : (gaussianReal 0 1) (Set.Ioc a b) ≠ 0 := by
    intro h0
    have := gaussianReal_absolutelyContinuous' 0 (v := 1) one_ne_zero h0
    rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at this
    linarith
  rw [h1, Ne, ENNReal.ofReal_eq_zero, not_le] at h2
  linarith

theorem concaveOn_Phi : ConcaveOn ℝ (Set.Ici 0) Φ := by
  refine AntitoneOn.concaveOn_of_deriv (convex_Ici 0) continuous_Phi.continuousOn
    (fun x _ => (hasDerivAt_Phi x).differentiableAt.differentiableWithinAt) ?_
  rw [interior_Ici]
  intro x hx y hy hxy
  rw [(hasDerivAt_Phi x).deriv, (hasDerivAt_Phi y).deriv, gaussianPDFReal_def]
  simp only [sub_zero, NNReal.coe_one, mul_one]
  gcongr
  exact le_of_lt hx

end GlynnSTSThm48

open GlynnSTSThm48 in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B)
    (g : C(unitInterval, ℝ) → ℝ) (hg : GlynnSTS.Limit.ClassM P B g)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (z : ℝ) (hz : GlynnSTS.Length.H P B g z = 1 - δ / 2)
    (p : ℝ) (hp : cdf (gaussianReal 0 1) p = 1 - δ / 2) :
    ENNReal.ofReal p ≤
      (∫⁻ ω, ENNReal.ofReal (g (B ω)) ∂P) * ENNReal.ofReal z := by
  have h29 := GlynnSTS.Length.display_2_9 P B hB g hg z
  have hmeas : AEMeasurable (fun ω => g (B ω)) P := (hg.1.comp hB.1).aemeasurable
  have hposP : ∀ᵐ ω ∂P, 0 < g (B ω) := hg.2.2.2.1
  have hpos : ∀ᵐ y ∂(P.map (fun ω => g (B ω))), y ∈ Set.Ioi (0 : ℝ) :=
    (ae_map_iff hmeas measurableSet_Ioi).2 hposP
  rw [Measure.restrict_eq_self_of_ae_mem hpos] at h29
  have hcm : ∀ c : ℝ, AEStronglyMeasurable (fun y => Φ (c * y)) (P.map (fun ω => g (B ω))) :=
    fun c => (continuous_Phi.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  rw [integral_map hmeas (hcm z)] at h29
  -- now `h29 : H z = ∫ Φ (z * g (B ω)) dP`
  have hpz : Φ p = ∫ ω, Φ (z * g (B ω)) ∂P := by
    simp only [Φ]; rw [hp, ← hz, h29]
  rcases le_or_gt z 0 with hz0 | hz0
  · -- the case `z ≤ 0`: then `p ≤ 0`
    have hle : ∫ ω, Φ (z * g (B ω)) ∂P ≤ ∫ _ω, Φ 0 ∂P := by
      refine integral_mono_ae ?_ (integrable_const _) ?_
      · refine Integrable.of_bound (C := 1)
          ((continuous_Phi.comp (continuous_const.mul continuous_id)).comp_aestronglyMeasurable
            hmeas.aestronglyMeasurable) (Eventually.of_forall (fun ω => ?_))
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [cdf_nonneg (gaussianReal 0 1) (z * g (B ω))], cdf_le_one _ _⟩
      · filter_upwards [hposP] with ω hω
        exact strictMono_Phi.monotone (mul_nonpos_of_nonpos_of_nonneg hz0 hω.le)
    rw [integral_const, probReal_univ, one_smul, ← hpz] at hle
    have hp0 : p ≤ 0 := strictMono_Phi.le_iff_le.1 hle
    rw [ENNReal.ofReal_of_nonpos hp0]; exact bot_le
  · set E := ∫⁻ ω, ENNReal.ofReal (g (B ω)) ∂P with hE
    by_cases hEtop : E = ∞
    · rw [hEtop, ENNReal.top_mul (by simpa using hz0)]; exact le_top
    -- integrability of `g ∘ B`
    have hint : Integrable (fun ω => g (B ω)) P := by
      refine ⟨hmeas.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (hposP.mono fun ω h => h.le)]
      exact lt_top_iff_ne_top.2 hEtop
    have hEm : E = ENNReal.ofReal (∫ ω, g (B ω) ∂P) := by
      rw [hE, ofReal_integral_eq_lintegral_ofReal hint (hposP.mono fun ω h => h.le)]
    have hJ := concaveOn_Phi.le_map_integral (μ := P) (f := fun ω => z * g (B ω))
      continuous_Phi.continuousOn isClosed_Ici
      (hposP.mono fun ω h => (show (0:ℝ) ≤ z * g (B ω) by positivity))
      (hint.const_mul z)
      (Integrable.of_bound (C := 1)
        ((continuous_Phi.comp (continuous_const.mul continuous_id)).comp_aestronglyMeasurable
          hmeas.aestronglyMeasurable) (Eventually.of_forall (fun ω => by
            simp only [Function.comp_apply]
            rw [Real.norm_eq_abs, abs_le]
            exact ⟨by linarith [cdf_nonneg (gaussianReal 0 1) (z * g (B ω))],
              cdf_le_one _ _⟩)))
    rw [← hpz, integral_const_mul] at hJ
    have hple : p ≤ z * ∫ ω, g (B ω) ∂P := strictMono_Phi.le_iff_le.1 hJ
    rw [hEm, ← ENNReal.ofReal_mul (integral_nonneg_of_ae (hposP.mono fun ω h => h.le))]
    apply ENNReal.ofReal_le_ofReal
    linarith [hple, mul_comm z (∫ ω, g (B ω) ∂P)]
