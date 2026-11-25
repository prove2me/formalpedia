-- Prove2me | solution 1 for GlobalTheory.splitTorus_hom_abelian_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:31:57.369809+00:00
-- url     : https://prove2.me/submissions/7a889fda-e5b0-4e6a-bbeb-7133196e11b6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialLocal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SplitTorusHomPullbackLocalTrivial
import Theorems.Thm_GlobalTheory_splitTorus_hom_pullback_local_trivial
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm
import Theorems.Thm_GlobalTheory_hom_ext_of_fromSpecStalk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over S) [GrpObj B], IsAbelianScheme B → ∀ f : splitTorus S X ⟶ B, IsMonHom f → f = 1 := by
  intro S _ X _ _ _ B _ hB f hf
  have := hB.proper
  refine Over.OverMorphism.ext (hom_ext_of_fromSpecStalk fun t ↦ ?_)
  let p := S.fromSpecStalk ((splitTorus S X).hom t)
  have h : (Over.pullback p).map f = (Over.pullback p).map (toUnit _ ≫ η[B]) :=
    splitTorus_hom_pullback_local_trivial _ p X B f hf
  have h₁ : ∀ u : splitTorus S X ⟶ B, ((Over.pullback p).map u).left ≫ pullback.fst B.hom p =
      pullback.fst (splitTorus S X).hom p ≫ u.left := fun u ↦ pullback.lift_fst _ _ _
  have h₂ : pullback.fst (splitTorus S X).hom p ≫ f.left =
      pullback.fst (splitTorus S X).hom p ≫ (1 : splitTorus S X ⟶ B).left := by
    rw [← h₁, ← h₁, h, Hom.one_def]
  have h₃ : pullback.lift ((splitTorus S X).left.fromSpecStalk t)
      (Spec.map ((splitTorus S X).hom.stalkMap t)) (Scheme.SpecMap_stalkMap_fromSpecStalk _).symm ≫
      pullback.fst (splitTorus S X).hom p = (splitTorus S X).left.fromSpecStalk t :=
    pullback.lift_fst _ _ _
  rw [← h₃, Category.assoc, Category.assoc, h₂]
end GlobalTheory
