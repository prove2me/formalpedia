-- Prove2me | solution 1 for GlobalTheory.UU.PackageDescent.exists_lift_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:56:14.663835+00:00
-- url     : https://prove2.me/submissions/0c9d0b76-97c4-426c-916a-2050900cc36d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubeDescendsAlongEtaleIsogeny
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubTrivDeltaAndEvenUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsDescendThrough
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.PackageDescent
variable {S : Scheme.{0}} {G B : Over S} (q : G ⟶ B) [Flat q.left] [Surjective q.left]
namespace GlobalTheory.UU.PackageDescent
theorem _root_.solution {T : Over S} (x : T ⟶ B) :
    ∃ (T' : Over S) (ρ : T' ⟶ T) (x' : T' ⟶ G), Flat ρ.left ∧ Surjective ρ.left ∧ x' ≫ q = ρ ≫ x := by
  refine ⟨Over.mk (pullback.fst x.left q.left ≫ T.hom), Over.homMk (pullback.fst x.left q.left) rfl,
    Over.homMk (pullback.snd x.left q.left) ?_, ?_, ?_, Over.OverMorphism.ext pullback.condition.symm⟩
  · show _ = pullback.fst x.left q.left ≫ T.hom
    rw [← Over.w q, ← Over.w x, pullback.condition_assoc]
  · show Flat (pullback.fst x.left q.left); infer_instance
  · show Surjective (pullback.fst x.left q.left); infer_instance
end GlobalTheory.UU.PackageDescent
