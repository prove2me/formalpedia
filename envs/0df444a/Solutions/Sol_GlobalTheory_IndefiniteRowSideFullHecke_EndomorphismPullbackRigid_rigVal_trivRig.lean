-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid.rigVal_trivRig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:38:36.557899+00:00
-- url     : https://prove2.me/submissions/de2f59d6-ac32-46d8-8a80-f51fdc29cb42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_EndomorphismPullbackRigid

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
variable {X : Scheme.{0}} {A : Over X}
variable [GrpObj A] [IsCommMonObj A]
namespace GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid
theorem _root_.solution (W : Over X) (i) (hi) : rigVal (trivRig A) W i hi = 1 :=
  map_one _
end GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid
