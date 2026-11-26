-- Prove2me | solution 1 for Malliavin.condExp_natural_filtrationPred_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:57:34.106995+00:00
-- url     : https://prove2.me/submissions/de254cdd-d19c-4152-8739-5fa65e0a447f

import Definitions.Def_Malliavin_PointwiseCondExp
import Definitions.Def_Malliavin_NaturalFiltrationLeftContinuous
import Theorems.Thm_Malliavin_condExp_filtrationPred_ae_eq_of_ae_sets
import Theorems.Thm_Malliavin_aestronglyMeasurable_brownian_filtrationPred
import Theorems.Thm_Malliavin_IsWienerGenerated_measurable
import Theorems.Thm_Malliavin_natural_eq_filtrationPred_sup


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ s, StronglyMeasurable (B s)) (t : ℝ≥0) (ht : 0 < t)
    (X : W → ℝ) (hX : Integrable X P) :
    P[X | filtrationPred (Filtration.natural B hm) t] =ᵐ[P]
      P[X | Filtration.natural B hm t] := by
  have hBt : AEStronglyMeasurable[filtrationPred (Filtration.natural B hm) t] (B t) P :=
    aestronglyMeasurable_brownian_filtrationPred hB hm t ht
  have hBtEventually : EventuallyMeasurable
      (filtrationPred (Filtration.natural B hm) t) (ae P) (B t) :=
    hBt.stronglyMeasurable_mk.measurable.eventuallyMeasurable.congr hBt.ae_eq_mk
  have hNaturalCompletion : Filtration.natural B hm t ≤
      eventuallyMeasurableSpace (filtrationPred (Filtration.natural B hm) t) (ae P) := by
    rw [natural_eq_filtrationPred_sup hm t]
    exact sup_le le_eventuallyMeasurableSpace hBtEventually.comap_le
  apply condExp_filtrationPred_ae_eq_of_ae_sets (Filtration.natural B hm) t
  · intro s hs
    exact hNaturalCompletion s hs
  · exact hX
end Malliavin
