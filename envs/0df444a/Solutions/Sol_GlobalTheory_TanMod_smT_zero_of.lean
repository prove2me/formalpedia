-- Prove2me | solution 1 for GlobalTheory.TanMod.smT_zero_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:40:18.385537+00:00
-- url     : https://prove2.me/submissions/84d842b4-d6a2-4c05-8372-7c884ad26c7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroup
import Theorems.Thm_GlobalTheory_TanMod_smT_left
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
theorem _root_.solution (W : overAt x0 (DualNumber S) ⟶ G)
    (hv : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ W.left = (1 : Over.mk x0 ⟶ G).left) :
    smT x0 0 W = 1 := by
  have he : epsMul (0 : S) = (algebraMap S (DualNumber S)).comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
    apply RingHom.ext
    intro r
    ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  let φ : overAt x0 (DualNumber S) ⟶ Over.mk x0 := Over.homMk (spMap (algebraMap S (DualNumber S))) rfl
  have h1 : (φ ≫ (1 : Over.mk x0 ⟶ G)) = 1 := MonObj.comp_one φ
  apply Over.OverMorphism.ext
  rw [← h1, smT_left]
  simp only [Over.homMk_left, Over.comp_left, φ]
  rw [he, ← spMap_comp', Category.assoc, hv]
end GlobalTheory.TanMod
