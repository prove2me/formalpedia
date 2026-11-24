-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent.vecEquiv_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:40:13.062463+00:00
-- url     : https://prove2.me/submissions/80790b69-5942-4393-9fc8-b6a27f38c8a2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SemiAbelianAxisTangent

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
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent
theorem _root_.solution {X : Scheme.{0}} {d : ℕ} {T : Over X} :
    vecEquiv T (1 : T ⟶ vecObj X d) = 1 :=
  ((yonedaGrpObjIsoOfRepresentableBy _ _ (vecRep X d)).hom.app (Opposite.op T)).hom.map_one
end GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent
