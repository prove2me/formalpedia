-- Prove2me | solution 1 for Kyprianou.Ch04.aeFiniteExpectedAbsoluteRandomIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:51:33.84133+00:00
-- url     : https://prove2.me/submissions/38efdf83-b44e-4ceb-b513-7bdeda621879

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

/-- Finite expected absolute mass yields a.e pathwise and outer integrability. -/
theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (R : Omega → Measure E)
    (f : Omega → E → ℝ)
    (hm : ∀ᵐ w ∂P, AEStronglyMeasurable (f w) (R w))
    (hL : AEMeasurable (fun w => ∫⁻ z, ENNReal.ofReal |f w z| ∂(R w)) P)
    (hLp : AEMeasurable (fun w => ∫⁻ z, ENNReal.ofReal (f w z) ∂(R w)) P)
    (hLn : AEMeasurable (fun w => ∫⁻ z, ENNReal.ofReal (-f w z) ∂(R w)) P)
    (hfin : (∫⁻ w, ∫⁻ z, ENNReal.ofReal |f w z| ∂(R w) ∂P) < ⊤) :
    (∀ᵐ w ∂P, Integrable (f w) (R w)) ∧
    Integrable (fun w => ∫ z, |f w z| ∂(R w)) P ∧
    (∫ w, ∫ z, |f w z| ∂(R w) ∂P) =
      (∫⁻ w, ∫⁻ z, ENNReal.ofReal |f w z| ∂(R w) ∂P).toReal ∧
    Integrable (fun w => ∫ z, f w z ∂(R w)) P := by
  let L (w : Omega) := ∫⁻ z, ENNReal.ofReal |f w z| ∂(R w)
  have ht := ae_lt_top' hL hfin.ne
  have hpath : ∀ᵐ w ∂P, Integrable (f w) (R w) := by
    filter_upwards [hm, ht] with w hw hwt
    refine ⟨hw, ?_⟩
    apply (hasFiniteIntegral_iff_norm (f w)).2
    simpa only [Real.norm_eq_abs] using hwt
  have he : (fun w => ∫ z, |f w z| ∂(R w)) =ᵐ[P] fun w => (L w).toReal := by
    filter_upwards [hm] with w hw
    exact integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun z => abs_nonneg (f w z))
      (by simpa only [Real.norm_eq_abs] using hw.norm)
  have hto : (fun w => ENNReal.ofReal (L w).toReal) =ᵐ[P] L := by
    filter_upwards [ht] with w hw
    exact ENNReal.ofReal_toReal hw.ne
  have hi : Integrable (fun w => (L w).toReal) P := by
    refine ⟨hL.ennreal_toReal.aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)).2
      (by rwa [lintegral_congr_ae hto])
  have habs : Integrable (fun w => ∫ z, |f w z| ∂(R w)) P :=
    (integrable_congr he).2 hi
  have hreal : AEStronglyMeasurable (fun w => ∫ z, f w z ∂(R w)) P := by
    apply (hLp.ennreal_toReal.sub hLn.ennreal_toReal).aestronglyMeasurable.congr
    filter_upwards [hpath] with w hw
    exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hw).symm
  refine ⟨hpath, habs, ?_, ?_⟩
  · rw [integral_congr_ae he, integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hi.aestronglyMeasurable,
      lintegral_congr_ae hto]
  · apply habs.mono' hreal
    exact Eventually.of_forall fun w => by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (f w)
