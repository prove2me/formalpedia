-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid.isoVal_trivIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:38:35.818881+00:00
-- url     : https://prove2.me/submissions/e2862e08-fc03-4d1e-a14e-6e1acb584492

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
theorem _root_.solution {T W : Over X} (f : T ⊗ A ⟶ A) (a b : ℤ) (t : W ⟶ T) (v u : W ⟶ A)
    (hu : lift t v ≫ f = u) (i j) (hi) (hj) : isoVal (trivIso f a b) t v u hu i j hi hj = 1 :=
  map_one _
end GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid
