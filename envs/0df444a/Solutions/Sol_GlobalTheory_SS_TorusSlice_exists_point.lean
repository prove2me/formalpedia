-- Prove2me | solution 1 for GlobalTheory.SS.TorusSlice.exists_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:34:45.004094+00:00
-- url     : https://prove2.me/submissions/f6fe9be8-bfae-4fd0-bf72-4dfa55490a42

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
theorem _root_.solution {k : Type} [Field k] [IsAlgClosed k] (G : Over (Sp k)) [LocallyOfFiniteType G.hom]
    {Z : Set G.left} (hZ : Z.Nonempty) (h : IsLocallyClosed Z) :
    ∃ p : 𝟙_ (Over (Sp k)) ⟶ G, ∀ s, p.left s ∈ Z := by
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  obtain ⟨x, hx, hc⟩ := nonempty_inter_closedPoints hZ h
  exact ⟨Over.homMk (pointOfClosedPoint (K := k) G.hom x hc) (pointOfClosedPoint_comp (K := k) G.hom x hc),
    fun s => (pointOfClosedPoint_apply (K := k) G.hom x hc s).symm ▸ hx⟩
end GlobalTheory.SS.TorusSlice
