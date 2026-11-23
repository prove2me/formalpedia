-- Prove2me | solution 1 for GlobalTheory.TanMod.unit_of_smT_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:24:04.263684+00:00
-- url     : https://prove2.me/submissions/ba07a042-86cf-4452-9c95-6c141474c471

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroup
import Theorems.Thm_P2M_GlobalTheory_TanMod_spMap_comp__ec2060aa7fa9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TanMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
variable {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)
variable {G : Over X0} [GrpObj G]
namespace GlobalTheory.TanMod
theorem _root_.solution (W : overAt x0 (DualNumber S) ⟶ G) (h : smT x0 0 W = 1) :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ W.left = (1 : Over.mk x0 ⟶ G).left := by
  have hid : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
    apply RingHom.ext
    intro r
    simp
  let ψ : Over.mk x0 ⟶ overAt x0 (DualNumber S) := Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
    show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) ≫ x0 = x0
    rw [← Category.assoc, spMap_comp', hid]
    simp [spMap])
  have hψ : ψ ≫ homAt x0 (tm ((0 : S) • (LinearMap.id : S →ₗ[S] S))) = ψ := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, ψ, Over.homMk_left, homAt]
    rw [spMap_comp']
    congr 1
    apply RingHom.ext
    intro r
    simp
  have h1 : ψ ≫ W = 1 := by
    rw [← hψ, Category.assoc]
    change ψ ≫ smT x0 0 W = 1
    rw [h, MonObj.comp_one]
  exact congrArg (fun φ => φ.left) h1
end GlobalTheory.TanMod
