-- Prove2me | solution 1 for Malliavin.IteratedIntegralConstruction.hasSum_simplexIntegralLI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:35.775985+00:00
-- url     : https://prove2.me/submissions/2404c351-39d2-4be6-9a39-96fa65973f69

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
theorem _root_.solution (hB : IsPreBrownianReal B P) (f : PositiveKernelSum) :
    HasSum (fun n ↦ simplexIntegralLI hB n (f n))
      ((positiveIteratedTowerLI hB f : CenteredRandomL2 hB) : RandomL2 P) := by
  have hsum := lp.hasSum_single (E := fun n : ℕ ↦ SimplexKernel (n + 1))
    (p := (2 : ℝ≥0∞)) (by norm_num) f
  have himage := ((CenteredRandomL2 hB).subtypeₗᵢ.comp
    (positiveIteratedTowerLI hB)).toContinuousLinearMap.hasSum hsum
  convert himage using 1
  · funext n
    rw [simplexIntegralLI_apply]
    rfl
  · rfl
end Malliavin.IteratedIntegralConstruction
