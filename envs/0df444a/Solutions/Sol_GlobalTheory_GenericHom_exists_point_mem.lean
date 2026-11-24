-- Prove2me | solution 1 for GlobalTheory.GenericHom.exists_point_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:45:13.664976+00:00
-- url     : https://prove2.me/submissions/7cf70a42-a6bc-4c71-b6e2-6ceeb03e722e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsMonHomExtension

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
open GlobalTheory GlobalTheory.GenericHom
variable {k : Type} [Field k] [IsAlgClosed k]
namespace GlobalTheory.GenericHom
theorem _root_.solution (X : Over (Sp k)) [LocallyOfFiniteType X.hom] (W : Set X.left)
    (hW : IsLocallyClosed W) (hne : W.Nonempty) :
    ∃ x : 𝟙_ (Over (Sp k)) ⟶ X, ∀ p, x.left p ∈ W := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨c, hcW, hc⟩ := nonempty_inter_closedPoints hne hW
  exact ⟨Over.homMk (pointOfClosedPoint (K := k) X.hom c hc) (pointOfClosedPoint_comp (K := k) X.hom c hc),
    fun p => (congrArg (· ∈ W) (pointOfClosedPoint_apply (K := k) X.hom c hc p)).mpr hcW⟩
end GlobalTheory.GenericHom
