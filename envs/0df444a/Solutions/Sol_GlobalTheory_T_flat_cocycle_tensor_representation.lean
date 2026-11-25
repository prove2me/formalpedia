-- Prove2me | solution 1 for GlobalTheory.T.flat_cocycle_tensor_representation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:00.749469+00:00
-- url     : https://prove2.me/submissions/49cf4cd5-1f4c-49ac-a05a-b19661dbd461

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FlatCocycleTensorRepresentation
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FlatCocycleTensorRepresentationStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_cocycle_of_flat


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
    (N : Type) [AddCommGroup N] [Module R N] [Module.Flat R N] (f : ∀ (T T' : C) (_ : T ⟶ T'), F.obj T' ⊗[R] N),
    (∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      f T T'' (φ ≫ ψ) = (mp F ψ).toLinearMap.rTensor N (f T T' φ) + f T' T'' ψ) →
    ∃ t : Z1 F ⊗[R] N, ∀ (T T' : C) (φ : T ⟶ T'), (evZ F φ).rTensor N t = f T T' φ := by
  first | exact @GlobalTheory.CompanionTheory.Axis.cocycle_of_flat | exact GlobalTheory.CompanionTheory.Axis.cocycle_of_flat | (intros; apply GlobalTheory.CompanionTheory.Axis.cocycle_of_flat <;> assumption)
end _root_.GlobalTheory.T
