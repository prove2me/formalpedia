-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback.GrpHom.pullCube_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:50:48.822325+00:00
-- url     : https://prove2.me/submissions/a7a9833b-5b3c-4678-92d3-e63311b9c0a0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_GroupHomPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
universe u
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S S' : Scheme.{u}}
open GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback.GrpHom
variable {G' : Over S'} [GrpObj G'] [IsCommMonObj G'] {G : Over S} [GrpObj G] [IsCommMonObj G]
  (f : GrpHom G' G)
namespace GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback.GrpHom
theorem _root_.solution (L : LB G.left) {t : LB.Gen (Theta G L)} (ht : t.IsGen) :
    (f.pullCube L t).IsGen :=
  genSquare_isGen L (φ := thφ G (x3 G)) (φ' := thφ G' (x3 G')) f.cube_sq thε ht
end GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback.GrpHom
