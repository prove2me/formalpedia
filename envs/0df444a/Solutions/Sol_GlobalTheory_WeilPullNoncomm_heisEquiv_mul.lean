-- Prove2me | solution 1 for GlobalTheory.WeilPullNoncomm.heisEquiv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:11:33.40858+00:00
-- url     : https://prove2.me/submissions/cbce3e90-8017-4a34-b9cd-55b221166060

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotWeilIsGrpPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeilPullNoncomm
open GlobalTheory.CommPairing
variable {S : Scheme.{0}} {G : Over S} [GrpObj G]
namespace GlobalTheory.WeilPullNoncomm
theorem _root_.solution {S : Scheme.{0}} {T : Over S} (x y : T ⟶ heisObj S) :
    heisEquiv T (x * y) = heisEquiv T x * heisEquiv T y :=
  ((yonedaGrpObjIsoOfRepresentableBy _ _ (heisRep S)).hom.app (Opposite.op T)).hom.map_mul x y
end GlobalTheory.WeilPullNoncomm
