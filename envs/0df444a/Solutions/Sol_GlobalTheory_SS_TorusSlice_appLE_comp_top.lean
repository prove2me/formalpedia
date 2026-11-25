-- Prove2me | solution 1 for GlobalTheory.SS.TorusSlice.appLE_comp_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:34:49.821235+00:00
-- url     : https://prove2.me/submissions/309635d5-79ce-49e4-b01b-6375972eab7c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorusStableGoodOpenOfWeightUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.TorusSlice
variable {S : Scheme.{0}}
variable {X : Type} [AddCommGroup X]
namespace GlobalTheory.SS.TorusSlice
theorem _root_.solution {Z Y G : Over S} (y : Z ⟶ Y) (f : Y ⟶ G) (g : Z ⟶ G) (e : g = y ≫ f) (U : G.left.Opens)
    (h : ⊤ ≤ g.left ⁻¹ᵁ U) (h' : ⊤ ≤ f.left ⁻¹ᵁ U) (u : Γ(G.left, U)) :
    (g.left.appLE U ⊤ h).hom u = y.left.appTop.hom ((f.left.appLE U ⊤ h').hom u) := by
  subst e
  have := Scheme.Hom.appLE_comp_appLE y.left f.left U ⊤ ⊤ h' le_top
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact (congrArg (fun φ => φ.hom u) this).symm
end GlobalTheory.SS.TorusSlice
