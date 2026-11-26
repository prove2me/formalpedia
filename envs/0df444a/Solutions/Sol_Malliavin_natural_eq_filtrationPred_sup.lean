-- Prove2me | solution 1 for Malliavin.natural_eq_filtrationPred_sup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:34.476567+00:00
-- url     : https://prove2.me/submissions/6e16090d-f24a-48df-88e2-8d8d709337c4

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
import Theorems.Thm_Malliavin_filtrationPred_natural

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
variable {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin
theorem _root_.solution (hm : ∀ s, StronglyMeasurable (B s)) (t : ℝ≥0) :
    Filtration.natural B hm t
      = filtrationPred (Filtration.natural B hm) t
        ⊔ MeasurableSpace.comap (B t) inferInstance := by
  apply le_antisymm
  · refine iSup₂_le fun j hjt ↦ ?_
    rcases lt_or_eq_of_le hjt with hj | hj
    · refine le_sup_of_le_left ?_
      rw [filtrationPred_natural hm]
      exact le_iSup₂ (f := fun (j : ℝ≥0) (_ : j < t) ↦
        MeasurableSpace.comap (B j) inferInstance) j hj
    · subst hj
      exact le_sup_right
  · refine sup_le (iSup₂_le fun s hst ↦ (Filtration.natural B hm).mono hst.le) ?_
    exact le_iSup₂ (f := fun (j : ℝ≥0) (_ : j ≤ t) ↦
      MeasurableSpace.comap (B j) inferInstance) t le_rfl
end Malliavin
