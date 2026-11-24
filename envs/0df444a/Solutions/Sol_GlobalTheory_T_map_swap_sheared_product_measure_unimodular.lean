-- Prove2me | solution 1 for GlobalTheory.T.map_swap_sheared_product_measure_unimodular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:21:16.435931+00:00
-- url     : https://prove2.me/submissions/defdf797-9747-481c-97be-b14803525957

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MapSwapShearedProductMeasureUnimodular
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MapSwapShearedProductMeasureUnimodularStatement
import Theorems.Thm_GlobalTheory_UnfoldNormal_map_swap_map_shear


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (ν : Measure H) [ν.IsHaarMeasure] (N : Subgroup H), IsClosed (N : Set H) → ∀ (κ : Measure N), κ.IsHaarMeasure → κ.map (fun n => n⁻¹) = κ → ((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)).map Prod.swap = (κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N) := by
  first | exact @GlobalTheory.UnfoldNormal.map_swap_map_shear | exact GlobalTheory.UnfoldNormal.map_swap_map_shear | (intros; apply GlobalTheory.UnfoldNormal.map_swap_map_shear <;> assumption)
end _root_.GlobalTheory.T
