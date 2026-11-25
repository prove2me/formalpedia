-- Prove2me | solution 1 for GlobalTheory.T.cocycle_tensor_coboundary_class_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:06.774143+00:00
-- url     : https://prove2.me/submissions/859ce3c9-72a8-4859-91d7-f493829d1676

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CocycleTensorCoboundaryClassZero
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CocycleTensorCoboundaryClassZeroStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_KFlat_class_eq_zero_of_coboundary


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] [Finite C] [Quiver.IsThin C] (F : C ⥤ CommAlgCat.{0} R)
    (N : Type) [AddCommGroup N] [Module R N] [Module.Flat R N] (t : Z1 F ⊗[R] N) (g : ∀ T : C, F.obj T ⊗[R] N),
    (∀ (T T' : C) (φ : T ⟶ T'), (evZ F φ).rTensor N t = g T' - (mp F φ).toLinearMap.rTensor N (g T)) →
    (H1.mk F).rTensor N t = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Axis.KFlat.class_eq_zero_of_coboundary | exact GlobalTheory.CompanionTheory.Axis.KFlat.class_eq_zero_of_coboundary | (intros; apply GlobalTheory.CompanionTheory.Axis.KFlat.class_eq_zero_of_coboundary <;> assumption)
end _root_.GlobalTheory.T
