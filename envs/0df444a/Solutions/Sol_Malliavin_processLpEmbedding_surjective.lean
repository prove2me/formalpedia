-- Prove2me | solution 1 for Malliavin.processLpEmbedding_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:51:30.633151+00:00
-- url     : https://prove2.me/submissions/2d955c37-de56-47d9-a351-bef446b7b973

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_Simplex
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_Malliavin_IteratedIntegral
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.mem_symmetricSubmodule


section
namespace Malliavin
open MeasureTheory
open scoped NNReal
universe u_1 u_2 u_3 u_4 u_7 u_8
universe u₁ u₂ u₃ u₄ u₅
variable {Ω : Type*} [MeasureSpace Ω]
section Step
variable {W : ℝ≥0 → Ω → ℝ}
end Step
section ContinuousTower
open ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace lp
variable {Ω' : Type*} [mΩ' : MeasurableSpace Ω'] {P : Measure Ω'}
  {B : ℝ≥0 → Ω' → ℝ}
private theorem measurePreserving_id_processTrim_symm
    (hmeas : ∀ t, Measurable (B t))
    (hgen : processMeasurableSpace B = mΩ') :
    @MeasurePreserving Ω' Ω' (processMeasurableSpace B) mΩ' id
      (processTrimMeasure P B hmeas) P := by
  let hm : processMeasurableSpace B ≤ mΩ' :=
    processMeasurableSpace_le_of_measurable hmeas
  have hm' : mΩ' ≤ processMeasurableSpace B := by rw [hgen]
  have hid : @Measurable Ω' Ω' (processMeasurableSpace B) mΩ' id :=
    @measurable_id'' Ω' mΩ' (processMeasurableSpace B) hm'
  apply @MeasurePreserving.mk Ω' Ω' (processMeasurableSpace B) mΩ' id
    (processTrimMeasure P B hmeas) P hid
  ext s hs
  have hsB : @MeasurableSet Ω' (processMeasurableSpace B) s := hm' s hs
  rw [Measure.map_apply hid hs, Set.preimage_id]
  exact trim_measurableSet_eq hm hsB
namespace IteratedIntegralConstruction
section HilbertBasisCountability
variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E]
end HilbertBasisCountability
end IteratedIntegralConstruction
namespace IteratedIntegralConstruction
end IteratedIntegralConstruction
namespace IteratedIntegralConstruction
end IteratedIntegralConstruction
end ContinuousTower
end Malliavin
end

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
namespace Malliavin
theorem _root_.solution
    (P : Measure Ω') (B : ℝ≥0 → Ω' → ℝ) (hmeas : ∀ t, Measurable (B t))
    (hgen : processMeasurableSpace B = mΩ') :
    Function.Surjective (processLpEmbedding P B hmeas) := by
  let hforward := measurePreserving_id_processTrim (P := P) hmeas
  let hreverse := measurePreserving_id_processTrim_symm (P := P) hmeas hgen
  let reverse : RandomL2 P →ₗᵢ[ℝ]
      (@Lp Ω' ℝ (processMeasurableSpace B) inferInstance 2
        (processTrimMeasure P B hmeas)) :=
    @Lp.compMeasurePreservingₗᵢ Ω' ℝ (processMeasurableSpace B) 2
      (processTrimMeasure P B hmeas) _ Ω' mΩ' P ℝ _ _ _ _ id hreverse
  intro f
  refine ⟨reverse f, ?_⟩
  change
    (@Lp.compMeasurePreserving Ω' ℝ mΩ' 2 P _ Ω'
      (processMeasurableSpace B) (processTrimMeasure P B hmeas) id hforward)
        ((@Lp.compMeasurePreserving Ω' ℝ (processMeasurableSpace B) 2
          (processTrimMeasure P B hmeas) _ Ω' mΩ' P id hreverse) f) = f
  have hcomp := @Lp.compMeasurePreserving_comp_apply Ω' ℝ mΩ' 2 P _ Ω'
    (processMeasurableSpace B) (processTrimMeasure P B hmeas) Ω'
    mΩ' P f id hreverse id hforward
  simpa only [Function.id_comp, Lp.compMeasurePreserving_id_apply] using hcomp.symm
end Malliavin
