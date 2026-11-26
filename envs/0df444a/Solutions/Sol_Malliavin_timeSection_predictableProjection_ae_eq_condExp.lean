-- Prove2me | solution 1 for Malliavin.timeSection_predictableProjection_ae_eq_condExp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:57.936182+00:00
-- url     : https://prove2.me/submissions/d9324346-8aff-4f9a-b1ac-f920555aaef8

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
import Theorems.Thm_Malliavin_filtrationPred_le
import Theorems.Thm_Malliavin_condExp_timeSection_predictableProjection_pred_ae
import Theorems.Thm_Malliavin_measurable_section_filtrationPred
import Theorems.Thm_Malliavin_memLp_timeSection_ae


set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution
    [SecondCountableTopology (RandomL2 P)] (U : TimeProcessL2 P)
    {G : ℝ≥0 × W → ℝ} (hG : StronglyMeasurable[𝓕.predictable] G)
    (hGae : (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ)
      =ᵐ[nonnegativeLebesgueMeasure.prod P] G) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
      (fun ω ↦ G (t, ω)) =ᵐ[P] P[(fun ω ↦ U (t, ω)) | filtrationPred 𝓕 t] := by
  have hsec := Measure.ae_ae_of_ae_prod hGae
  filter_upwards [condExp_timeSection_predictableProjection_pred_ae 𝓕 U, hsec,
    memLp_timeSection_ae (predictableProjection 𝓕 U : TimeProcessL2 P)] with t hct hst hQt hat
  have hGt : StronglyMeasurable[filtrationPred 𝓕 t] fun ω ↦ G (t, ω) :=
    hG.comp_measurable (measurable_section_filtrationPred 𝓕 hat)
  have hGint : Integrable (fun ω ↦ G (t, ω)) P :=
    (hQt.integrable one_le_two).congr hst
  calc (fun ω ↦ G (t, ω))
      = P[(fun ω ↦ G (t, ω)) | filtrationPred 𝓕 t] :=
        (condExp_of_stronglyMeasurable (filtrationPred_le 𝓕 t) hGt hGint).symm
    _ =ᵐ[P] P[(fun ω ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω)) |
          filtrationPred 𝓕 t] := condExp_congr_ae (hst.mono fun ω hω ↦ hω.symm)
    _ =ᵐ[P] P[(fun ω ↦ U (t, ω)) | filtrationPred 𝓕 t] := hct hat
end Malliavin
