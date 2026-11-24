-- Prove2me | solution 1 for GlobalTheory.T.smulInvariantMeasure_sheared_product_pairGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:20:52.615457+00:00
-- url     : https://prove2.me/submissions/4edaabc7-9536-47f4-8fe6-83f4d25dd65d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmulInvariantMeasureShearedProductPairGroup
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmulInvariantMeasureShearedProductPairGroupStatement
import Theorems.Thm_GlobalTheory_UnfoldNormal_smulInvariantMeasure_shear_map


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
theorem _root_.solution : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H), IsClosed (N : Set H) → ∀ (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N), κ.IsHaarMeasure → (∀ (γ : H) (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ) → SMulInvariantMeasure (GlobalTheory.UnfoldNormal.pairGroup Γ N hN) (H × H) ((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)) := by
  first | exact @GlobalTheory.UnfoldNormal.smulInvariantMeasure_shear_map | exact GlobalTheory.UnfoldNormal.smulInvariantMeasure_shear_map | (intros; apply GlobalTheory.UnfoldNormal.smulInvariantMeasure_shear_map <;> assumption)
end _root_.GlobalTheory.T
