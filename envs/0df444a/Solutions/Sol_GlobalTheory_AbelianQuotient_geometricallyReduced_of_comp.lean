-- Prove2me | solution 1 for GlobalTheory.AbelianQuotient.geometricallyReduced_of_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:08:20.750751+00:00
-- url     : https://prove2.me/submissions/eba1efd5-2205-4b59-b14c-db5a12efc36c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuotientIsAbelianSchemeOfQuotientScheme
import Theorems.Thm_GlobalTheory_AbelianQuotient_isReduced_of_flat_of_surjective

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
theorem _root_.solution {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z) [Flat p]
    [Surjective p] [h : GeometricallyReduced (p ≫ f)] : GeometricallyReduced f := by
  refine ⟨fun K _ y W a b hW => ?_⟩
  have : IsReduced (pullback p a) :=
    h.geometrically_isReduced y _ _ ((IsPullback.of_hasPullback p a).paste_vert hW)
  exact isReduced_of_flat_of_surjective (pullback.snd p a)
end GlobalTheory.AbelianQuotient
