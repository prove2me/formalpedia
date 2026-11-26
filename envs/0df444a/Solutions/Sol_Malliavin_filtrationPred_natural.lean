-- Prove2me | solution 1 for Malliavin.filtrationPred_natural
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:06.940069+00:00
-- url     : https://prove2.me/submissions/8644ea2c-b886-4588-8494-f904dbaabc2c

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
import Theorems.Thm_Malliavin_le_filtrationPred

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
    filtrationPred (Filtration.natural B hm) t
      = ⨆ (s : ℝ≥0) (_ : s < t), MeasurableSpace.comap (B s) inferInstance := by
  apply le_antisymm
  · refine iSup₂_le fun s hst ↦ iSup₂_le fun j hjs ↦ ?_
    exact le_iSup₂ (f := fun (j : ℝ≥0) (_ : j < t) ↦
      MeasurableSpace.comap (B j) inferInstance) j (lt_of_le_of_lt hjs hst)
  · refine iSup₂_le fun s hst ↦ le_trans ?_
      (le_filtrationPred (Filtration.natural B hm) hst)
    exact le_iSup₂ (f := fun (j : ℝ≥0) (_ : j ≤ s) ↦
      MeasurableSpace.comap (B j) inferInstance) s le_rfl
end Malliavin
