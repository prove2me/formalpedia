-- Prove2me | solution 1 for GlobalTheory.LaurentConst.quot_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:45:08.147504+00:00
-- url     : https://prove2.me/submissions/4810adf3-699f-43bf-b7e4-13ce1ba55b75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentConst
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {W Z : Scheme.{0}}
namespace GlobalTheory.LaurentConst
theorem _root_.solution {a b a' b' : Z ⟶ B.left} (h : b ≫ B.hom = a ≫ B.hom)
    (h' : b' ≫ B.hom = a' ≫ B.hom) (ha : a = a') (hb : b = b') : quot a b h = quot a' b' h' := by
  subst ha hb; rfl
end GlobalTheory.LaurentConst
