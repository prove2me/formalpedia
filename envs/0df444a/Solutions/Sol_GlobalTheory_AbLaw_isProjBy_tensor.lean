-- Prove2me | solution 1 for GlobalTheory.AbLaw.isProjBy_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:58:57.34487+00:00
-- url     : https://prove2.me/submissions/1e9b1a96-1384-4244-9728-d155e518deba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback
import Theorems.Thm_GlobalTheory_AbLaw_Segre_isProjBy_of_isPullback

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
open GlobalTheory.AbLaw
noncomputable section
namespace GlobalTheory.AbLaw
theorem _root_.solution : ∀ (R : Type) [CommRing R] (X Y : Over (Spec (CommRingCat.of R))),
    IsProjBy X.hom → IsProjBy Y.hom → IsProjBy (X ⊗ Y).hom := fun _ _ X Y hX hY =>
  GlobalTheory.AbLaw.Segre.isProjBy_of_isPullback _ _ (IsPullback.of_hasPullback X.hom Y.hom) hX hY
end GlobalTheory.AbLaw
