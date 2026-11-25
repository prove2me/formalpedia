-- Prove2me | solution 1 for Kyprianou.Ch04.nestedNonnegativeIntegralToReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T10:11:40.423916+00:00
-- url     : https://prove2.me/submissions/5821f479-5a27-4b73-b4aa-fa8a5d68eb77

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
open Kyprianou.Ch04

/-- Use the nonnegative Bochner integral identity on each section. -/
theorem solution
    (mu nu : Measure Real) [SigmaFinite nu]
    (f : Real × Real → Real) (hf : Measurable f) (hn : ∀ z, 0 ≤ f z)
    (hFin : (∫⁻ s, ∫⁻ x, ENNReal.ofReal (f (s,x)) ∂nu ∂mu) ≠ ⊤) :
    (∫ s, ∫ x, f (s,x) ∂nu ∂mu) =
      (∫⁻ s, ∫⁻ x, ENNReal.ofReal (f (s,x)) ∂nu ∂mu).toReal := by
  let L (s : ℝ) := ∫⁻ x, ENNReal.ofReal (f (s,x)) ∂nu
  have hL : Measurable L :=
    Measurable.lintegral_prod_right (f := fun s x => ENNReal.ofReal (f (s,x)))
      (ENNReal.measurable_ofReal.comp hf)
  have hn' (s : ℝ) : 0 ≤ ∫ x, f (s,x) ∂nu :=
    integral_nonneg (fun x => hn (s,x))
  have he (s : ℝ) : (∫ x, f (s,x) ∂nu) = (L s).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => hn (s,x))
      (hf.comp measurable_prodMk_left).aestronglyMeasurable
  simp_rw [he]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
    hL.ennreal_toReal.aestronglyMeasurable]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_lt_top hL hFin] with s hs
  exact ENNReal.ofReal_toReal hs.ne
