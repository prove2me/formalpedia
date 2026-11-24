-- Prove2me | solution 1 for GlobalTheory.SplitTorus.comm_bcMap_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:56:05.260108+00:00
-- url     : https://prove2.me/submissions/451c4974-66a6-427f-8013-cab4f0c7f253

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Theorems.Thm_GlobalTheory_SplitTorus_bcIso_hom_fst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [reassoc] GlobalTheory.SplitTorus.bcIso_hom_fst

set_option autoImplicit false
set_option autoImplicit false
universe u
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open AddMonoidAlgebra (single)
open GlobalTheory
open GlobalTheory.SplitTorus
variable {S S' : Scheme.{u}} (f : S' ⟶ S) (X Y : Type u) [AddCommGroup X] [AddCommGroup Y]
variable {X Y}
namespace GlobalTheory.SplitTorus
theorem _root_.solution (g : splitTorus S X ⟶ splitTorus S Y)
    (g' : splitTorus S' X ⟶ splitTorus S' Y) :
    g'.left ≫ bcMap f Y = bcMap f X ≫ g.left ↔
      g' ≫ (bcIso f Y).hom = (bcIso f X).hom ≫ (Over.pullback f).map g := by
  have A : ((Over.pullback f).map g).left ≫ pullback.fst (splitTorus S Y).hom f =
      pullback.fst (splitTorus S X).hom f ≫ g.left := pullback.lift_fst _ _ _
  have B : ((bcIso f X).hom ≫ (Over.pullback f).map g).left ≫ pullback.fst (splitTorus S Y).hom f =
      bcMap f X ≫ g.left := by
    rw [Over.comp_left, Category.assoc, A, bcIso_hom_fst_assoc]
  have C : (g' ≫ (bcIso f Y).hom).left ≫ pullback.fst (splitTorus S Y).hom f =
      g'.left ≫ bcMap f Y := by
    rw [Over.comp_left, Category.assoc, bcIso_hom_fst]
  refine ⟨fun h => Over.OverMorphism.ext (pullback.hom_ext ?_ ?_), fun h => by rw [← C, h, B]⟩
  · rw [B, C, h]
  · exact (Over.w _).trans (Over.w _).symm
end GlobalTheory.SplitTorus
