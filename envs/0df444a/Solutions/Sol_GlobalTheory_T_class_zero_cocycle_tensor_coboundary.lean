-- Prove2me | solution 1 for GlobalTheory.T.class_zero_cocycle_tensor_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:32:23.442462+00:00
-- url     : https://prove2.me/submissions/39748717-e3e1-462a-a3f5-ad2e87095454

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClassZeroCocycleTensorCoboundary
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClassZeroCocycleTensorCoboundaryStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_rTensor_cocycle_eq_coboundary_of_class_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (N : Type) [AddCommGroup N] [Module R N] (t : Z1 F ⊗[R] N), (H1.mk F).rTensor N t = 0 →
    ∃ g : ∀ T : C, F.obj T ⊗[R] N, ∀ (T T' : C) (φ : T ⟶ T'),
      (evZ F φ).rTensor N t = g T' - (mp F φ).toLinearMap.rTensor N (g T) := by
  first | exact @GlobalTheory.CompanionTheory.Axis.rTensor_cocycle_eq_coboundary_of_class_eq_zero | exact GlobalTheory.CompanionTheory.Axis.rTensor_cocycle_eq_coboundary_of_class_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Axis.rTensor_cocycle_eq_coboundary_of_class_eq_zero <;> assumption)
end _root_.GlobalTheory.T
