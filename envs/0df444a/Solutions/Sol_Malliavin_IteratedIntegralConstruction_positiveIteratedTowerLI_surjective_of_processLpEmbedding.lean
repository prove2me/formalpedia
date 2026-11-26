-- Prove2me | solution 1 for Malliavin.IteratedIntegralConstruction.positiveIteratedTowerLI_surjective_of_processLpEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:51:33.770041+00:00
-- url     : https://prove2.me/submissions/cfcd51ee-7145-4895-ac9a-436d19baa7b8

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_Simplex
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_Malliavin_IteratedIntegral

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
    (hmeas : ∀ t, Measurable (B t))
    (hexhausts : Function.Surjective (processLpEmbedding P B hmeas)) :
    Function.Surjective (positiveIteratedTowerLI hB) := by
  classical
  have hcondition : processMeasurableL2Exhausts P B := ⟨hmeas, hexhausts⟩
  rw [positiveIteratedTowerLI, dif_pos ⟨⟨inferInstance⟩, hcondition⟩]
  exact (Classical.choice (nonempty_positiveKernelSum_equiv_centered hB)).surjective
end Malliavin.IteratedIntegralConstruction
