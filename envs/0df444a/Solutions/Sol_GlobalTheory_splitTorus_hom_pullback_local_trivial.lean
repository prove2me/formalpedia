-- Prove2me | solution 1 for GlobalTheory.splitTorus_hom_pullback_local_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:01:29.637317+00:00
-- url     : https://prove2.me/submissions/ef57e9c4-8d43-48ac-bd33-380106125863

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
import Theorems.Thm_GlobalTheory_TorusLocal_pullback_map_eq_one
import Theorems.Thm_GlobalTheory_splitTorus_hom_proper_trivial_local


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
theorem _root_.solution {S : Scheme.{0}} (A : CommRingCat.{0}) [IsLocalRing A]
    [IsNoetherianRing A] (p : Spec A ⟶ S) (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (B : Over S) [GrpObj B] [IsProper B.hom] (f : splitTorus S X ⟶ B)
    (hf : IsMonHom f) :
    (Over.pullback p).map f = (Over.pullback p).map (toUnit _ ≫ η[B]) := by
  obtain ⟨A⟩ := A
  refine TorusLocal.pullback_map_eq_one p X B f hf fun g hg ↦ ?_
  have : IsProper ((Over.pullback p).obj B).hom := inferInstanceAs (IsProper (pullback.snd _ _))
  exact splitTorus_hom_proper_trivial_local A X _ g hg
end GlobalTheory
