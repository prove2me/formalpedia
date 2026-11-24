-- Prove2me | solution 1 for GlobalTheory.UnfoldNormal.map_swap_map_shear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:11:38.451047+00:00
-- url     : https://prove2.me/submissions/f486c8d1-29e9-48d2-8d56-c5bdd22a7389

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MapSwapShearedProductMeasureUnimodular
import Theorems.Thm_GlobalTheory_UnfoldNormal_measurableEmbedding_shear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Function
open scoped Pointwise
open GlobalTheory GlobalTheory.UnfoldNormal
namespace GlobalTheory.UnfoldNormal
theorem _root_.solution (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H]
    [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] (N : Subgroup H) (hNc : IsClosed (N : Set H))
    (κ : Measure N) (hκ : κ.IsHaarMeasure) (hinv : κ.map (fun n => n⁻¹) = κ) :
    ((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)).map Prod.swap
      = (κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N) := by
  haveI : LocallyCompactSpace N := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI := hκ
  have hsh : Measurable (shear N) := (measurableEmbedding_shear hNc).measurable
  have hT : MeasurePreserving (fun p : N × H => (p.1⁻¹, (p.1 : H) * p.2)) (κ.prod ν) (κ.prod ν) := by
    refine MeasurePreserving.skew_product (f := fun n : N => n⁻¹) (g := fun (n : N) (h : H) => (n : H) * h)
      ⟨measurable_inv, hinv⟩ ((measurable_subtype_coe.comp measurable_fst).mul measurable_snd) ?_
    exact Filter.Eventually.of_forall fun n => (measurePreserving_mul_left ν (n : H)).map_eq
  have hcomm : Prod.swap ∘ shear N = shear N ∘ (fun p : N × H => (p.1⁻¹, (p.1 : H) * p.2)) := by
    funext p
    simp [shear]
  rw [Measure.map_map measurable_swap hsh, hcomm, ← Measure.map_map hsh hT.measurable, hT.map_eq]
end GlobalTheory.UnfoldNormal
