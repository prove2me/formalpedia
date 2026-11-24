-- Prove2me | solution 1 for GlobalTheory.TorusExtBaseChange.isPullback_pullback_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:34:09.455232+00:00
-- url     : https://prove2.me/submissions/3196ced9-c498-4589-a52a-e8c1b8e9757b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPullbackPullbackMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusExtBaseChange
namespace GlobalTheory.TorusExtBaseChange
theorem _root_.solution {S S' : Scheme.{0}} (f : S' ⟶ S) {G B : Over S} (q : G ⟶ B) :
    IsPullback (pullback.fst G.hom f) ((Over.pullback f).map q).left q.left (pullback.fst B.hom f) := by
  have h1 : ((Over.pullback f).map q).left ≫ pullback.fst B.hom f = pullback.fst G.hom f ≫ q.left :=
    pullback.lift_fst _ _ _
  have h2 : ((Over.pullback f).map q).left ≫ pullback.snd B.hom f = pullback.snd G.hom f :=
    pullback.lift_snd _ _ _
  refine IsPullback.of_bot ?_ h1.symm (IsPullback.of_hasPullback B.hom f)
  rw [h2, Over.w q]
  exact IsPullback.of_hasPullback _ _
end GlobalTheory.TorusExtBaseChange
