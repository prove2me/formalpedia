-- Prove2me | solution 1 for GlobalTheory.DetExtend.lieMult_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:53:02.204311+00:00
-- url     : https://prove2.me/submissions/977c8804-2111-4f32-bf24-6b38e56dc340

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPushEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetCondIffOfFieldExtension
import Theorems.Thm_GlobalTheory_LiePull_lieMult_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


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
theorem _root_.solution {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S) {G : Over S} [GrpObj G] {O : Type}
    [CommRing O] (a : OAct O G) (a' : OAct O ((Over.pullback x).obj G))
    (h : ∀ c, a'.act c = (Over.pullback x).map (a.act c)) {k' : Type} [Field k'] (y : Sp k' ⟶ Sp k)
    (τ : O →+* k') (n : ℕ) : LieMult a' y τ n ↔ LieMult a (y ≫ x) τ n :=
  LiePull.lieMult_pull O _ _ G _ x _ a a' (isGrpPullback_pullback G x)
    (fun c => by rw [h]; exact pullback.lift_fst _ _ _) k' y τ n
end GlobalTheory.DetExtend
