-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid.trivIso_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:38:37.869852+00:00
-- url     : https://prove2.me/submissions/347359cd-af24-4f14-8177-492ddba60149

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
theorem _root_.solution {T : Over X} (f : T ⊗ A ⟶ A) (a b : ℤ) : (trivIso f a b).IsGen :=
  fun p q => by
    have h₁ : (PowOver (trivRig A).L a T).g p.1 q.1 = 1 := linComb_trivL_g _ _ _ _
    have h₂ : (PullPow (trivRig A).L f b).g p.2 q.2 = 1 := linComb_trivL_g _ _ _ _
    have h : (LB.div (PowOver (trivRig A).L a T) (PullPow (trivRig A).L f b)).g p q = 1 := by
      simp only [LB.div]
      rw [h₁, h₂, map_one, map_one, inv_one, _root_.mul_one]
      rfl
    rw [h, _root_.one_mul]
    exact (map_one _).trans (map_one _).symm
end GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid
