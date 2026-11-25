-- Prove2me | solution 1 for GlobalTheory.ZM.FamOf.snd_unitInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:44:31.358187+00:00
-- url     : https://prove2.me/submissions/ab7c93dc-2f41-410d-a82e-1a1e3f30e0be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DenseOfDenseP
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSectionsFam
import Theorems.Thm_GlobalTheory_ZM_FamOf_to_base_ext

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
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.FamOf
variable {S : Scheme.{0}} (A : Over S)
namespace GlobalTheory.ZM.FamOf
theorem _root_.solution : (snd (Over.mk (𝟙 S)) A).left ≫ (unitInv A).left = 𝟙 _ := by
  rw [← Over.comp_left]
  have : snd (Over.mk (𝟙 S)) A ≫ unitInv A = 𝟙 _ :=
    CartesianMonoidalCategory.hom_ext _ _ (to_base_ext _ _) (by simp [unitInv])
  rw [this]; rfl
end GlobalTheory.ZM.FamOf
