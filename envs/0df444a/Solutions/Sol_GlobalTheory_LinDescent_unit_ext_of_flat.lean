-- Prove2me | solution 1 for GlobalTheory.LinDescent.unit_ext_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:45:04.89944+00:00
-- url     : https://prove2.me/submissions/d17d55b3-a235-41ad-8b93-8d0c9bb639d6

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
import Theorems.Thm_GlobalTheory_FunDescent_app_injective


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
theorem _root_.solution [Flat π] [Surjective π] {V : Y.Opens} {a b : Γ(Y, V)ˣ}
    (h : ∀ x, π x ∈ V → gm (𝟙 X ≫ π) x V a = gm (𝟙 X ≫ π) x V b) : a = b := by
  refine Units.ext (FunDescent.app_injective π V (fn_ext fun x hx => ?_))
  rw [gs_pull (𝟙 X) π x V hx, gs_pull (𝟙 X) π x V hx, gs_unit (𝟙 X ≫ π) x V hx,
    gs_unit (𝟙 X ≫ π) x V hx, h x hx]
end GlobalTheory.LinDescent
