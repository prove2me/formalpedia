-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid.secVal_trivOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:38:37.188458+00:00
-- url     : https://prove2.me/submissions/6918a80a-5634-4056-9139-03cbbe5ad126

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
omit [IsCommMonObj A]
namespace GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid
theorem _root_.solution {T W : Over X} (k : ℤ) (t : W ⟶ T) (v : W ⟶ A) (i) (hi) :
    secVal (trivOne k T) t v i hi = 1 :=
  map_one _
end GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid
