-- Prove2me | solution 1 for GlobalTheory.DetExtend.exists_oAct_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:51:23.965016+00:00
-- url     : https://prove2.me/submissions/e7ebee76-4618-4c04-8f15-b40298865834

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPushEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetCondIffOfFieldExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.DetExtend
namespace GlobalTheory.DetExtend
theorem _root_.solution {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G] {O : Type} [CommRing O]
    (a : OAct O G) : ∃ a' : OAct O ((Over.pullback f).obj G), ∀ c, a'.act c = (Over.pullback f).map (a.act c) :=
  ⟨{ act := fun c => (Over.pullback f).map (a.act c)
     hom := fun c => by have := a.hom c; infer_instance
     one := by rw [a.one, CategoryTheory.Functor.map_id]
     mul := fun x y => by rw [a.mul, CategoryTheory.Functor.map_comp]
     add := fun x y => by rw [a.add]; exact CategoryTheory.Functor.map_mul _ _ _ }, fun _ => rfl⟩
end GlobalTheory.DetExtend
