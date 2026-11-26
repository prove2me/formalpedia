-- Prove2me | solution 1 for Malliavin.IteratedIntegralConstruction.positiveIteratedTowerLI_surjective_of_generated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:29.146688+00:00
-- url     : https://prove2.me/submissions/41516076-c3b2-4a9e-a4a6-f9d53ce4af7f

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_Simplex
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_Malliavin_IteratedIntegral
import Theorems.Thm_Malliavin_IsWienerGenerated_measurable
import Theorems.Thm_Malliavin_processLpEmbedding_surjective
import Theorems.Thm_Malliavin_IteratedIntegralConstruction_positiveIteratedTowerLI_surjective_of_processLpEmbedding

set_option autoImplicit false
open Malliavin
open MeasureTheory
open scoped NNReal
universe u_1 u_2 u_3 u_4 u_7 u_8
universe u₁ u₂ u₃ u₄ u₅
variable {Ω : Type*} [MeasureSpace Ω]
open ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace lp
variable {Ω' : Type*} [mΩ' : MeasurableSpace Ω'] {P : Measure Ω'}
  {B : ℝ≥0 → Ω' → ℝ}
open Malliavin.IteratedIntegralConstruction
attribute [local instance] Malliavin.IteratedIntegralConstruction.fact_two_ne_top
attribute [local instance] Malliavin.IteratedIntegralConstruction.simplexBasisIndex_countable
attribute [local instance] Malliavin.IteratedIntegralConstruction.globalBasisIndex_infinite
namespace Malliavin.IteratedIntegralConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P) [SecondCountableTopology (RandomL2 P)]
    (hgen : IsWienerGenerated B) :
    Function.Surjective (positiveIteratedTowerLI hB) := by
  let hmeas : ∀ t, Measurable (B t) := hgen.measurable
  exact positiveIteratedTowerLI_surjective_of_processLpEmbedding hB hmeas
    (processLpEmbedding_surjective P B hmeas hgen)
end Malliavin.IteratedIntegralConstruction
