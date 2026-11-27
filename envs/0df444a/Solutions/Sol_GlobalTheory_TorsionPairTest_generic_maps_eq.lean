-- Prove2me | solution 1 for GlobalTheory.TorsionPairTest.generic_maps_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:34:55.66019+00:00
-- url     : https://prove2.me/submissions/5927d483-0ce4-4790-b996-7a271135f536

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_InhTate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UniformisationSurvey_EquivIffOfIsEmpty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionPairTest
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}
namespace GlobalTheory.TorsionPairTest
theorem _root_.solution (W : (Spec (CommRingCat.of R)).Opens) (χ : D.X) :
    (jK R ∣_ W) ≫ (toUnit (TW W) ≫ D.c χ).left = (jK R ⁻¹ᵁ W).ι ≫ ptK (D.c χ) := by
  change (jK R ∣_ W) ≫ W.ι ≫ (D.c χ).left = (jK R ⁻¹ᵁ W).ι ≫ jK R ≫ (D.c χ).left
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
end GlobalTheory.TorsionPairTest
