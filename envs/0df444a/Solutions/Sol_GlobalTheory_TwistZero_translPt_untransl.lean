-- Prove2me | solution 1 for GlobalTheory.TwistZero.translPt_untransl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:58:10.226861+00:00
-- url     : https://prove2.me/submissions/265bfa11-c7a2-4f0f-8684-73373d47c1d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_TorsionZeroCountTwist
import Theorems.Thm_GlobalTheory_TwistZero_hom_base_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
  ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TwistZero
variable {S : Scheme.{0}} (A : Over S) [GrpObj A]
namespace GlobalTheory.TwistZero
theorem _root_.solution (b : baseOver S ⟶ A) : translPt A b ≫ untransl A b = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · exact hom_base_ext _ _
  · rw [untransl, Category.assoc, lift_snd, MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id,
      Category.id_comp, ← Category.assoc, hom_base_ext (translPt A b ≫ _) (fst _ _), translPt,
      ← Hom.mul_def, inv_mul_cancel_left]
end GlobalTheory.TwistZero
