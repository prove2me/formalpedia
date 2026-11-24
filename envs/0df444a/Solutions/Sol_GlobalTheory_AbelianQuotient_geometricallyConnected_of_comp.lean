-- Prove2me | solution 1 for GlobalTheory.AbelianQuotient.geometricallyConnected_of_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:32:38.426648+00:00
-- url     : https://prove2.me/submissions/8eed9781-6260-4b19-97da-3377676b2e84

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuotientIsAbelianSchemeOfQuotientScheme

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.AbelianQuotient
variable {S : Scheme.{0}}
namespace GlobalTheory.AbelianQuotient
theorem _root_.solution {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [Surjective p] [h : GeometricallyConnected (p ≫ f)] : GeometricallyConnected f := by
  refine ⟨fun K _ y W a b hW => ?_⟩
  have : ConnectedSpace ↥(pullback p a) :=
    h.geometrically_connectedSpace y _ _ ((IsPullback.of_hasPullback p a).paste_vert hW)
  exact (pullback.snd p a).surjective.connectedSpace (pullback.snd p a).continuous
end GlobalTheory.AbelianQuotient
