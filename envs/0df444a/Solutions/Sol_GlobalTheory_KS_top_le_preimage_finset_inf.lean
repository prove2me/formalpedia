-- Prove2me | solution 1 for GlobalTheory.KS.top_le_preimage_finset_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:29:51.096866+00:00
-- url     : https://prove2.me/submissions/04bb9bc3-8f06-4f22-a7b8-97eae672a021

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueUniformisingVectorVerticalTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFibreCoords

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS
namespace GlobalTheory.KS
theorem _root_.solution {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {κ : Type} (s : Finset κ) (W : κ → X.Opens)
    (h : ∀ i ∈ s, ⊤ ≤ x ⁻¹ᵁ W i) : ⊤ ≤ x ⁻¹ᵁ (s.inf W) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
    intro _ p _
    simp
  | @insert a s ha ih =>
    intro h p hp
    rw [Finset.inf_insert]
    exact ⟨h a (Finset.mem_insert_self a s) hp, ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) hp⟩
end GlobalTheory.KS
