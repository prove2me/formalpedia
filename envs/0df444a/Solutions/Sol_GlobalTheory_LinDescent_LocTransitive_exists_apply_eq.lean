-- Prove2me | solution 1 for GlobalTheory.LinDescent.LocTransitive.exists_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:45:09.21697+00:00
-- url     : https://prove2.me/submissions/730b8ea5-e224-44ac-80ce-dbbfee8a8be8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
variable {X Y Z : Scheme.{0}}
variable {L : LB X} {C : Type} {t : C → (X ⟶ X)} {π : X ⟶ Y}
namespace GlobalTheory.LinDescent
namespace LocTransitive
theorem _root_.solution (h : LocTransitive t π) {x x' : X} (e : π x = π x') :
    ∃ c, x = t c x' := by
  obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := π) x x' e
  obtain ⟨c, Z', a, _, z', rfl, h'⟩ := h _ _ _ (pullback.condition (f := π) (g := π)) z
  exact ⟨c, congrArg (fun q : Z' ⟶ X => q z') h'⟩
end LocTransitive
end GlobalTheory.LinDescent
