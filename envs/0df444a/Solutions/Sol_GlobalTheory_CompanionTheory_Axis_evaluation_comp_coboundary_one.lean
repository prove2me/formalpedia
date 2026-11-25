-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Axis.evaluation_comp_coboundary_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:19:01.210699+00:00
-- url     : https://prove2.me/submissions/5fe99afd-b876-434e-805c-57a69a7052c5

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FlatCocycleTensorRepresentation

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
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Axis
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
namespace GlobalTheory.CompanionTheory.Axis
theorem _root_.solution {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (LinearMap.proj (⟨T, T', T'', φ, ψ⟩ : Σ T : C, Σ T' : C, Σ T'' : C, (T ⟶ T') × (T' ⟶ T'')) :
        (∀ a : (Σ T : C, Σ T' : C, Σ T'' : C, (T ⟶ T') × (T' ⟶ T'')), F.obj a.2.2.1) →ₗ[R] _) ∘ₗ
      (twoCochainsPiComposableEquiv F).toLinearMap ∘ₗ d1 F =
    (mp F ψ).toLinearMap ∘ₗ evC F φ - evC F (φ ≫ ψ) + evC F ψ := by
  ext f
  rfl
end GlobalTheory.CompanionTheory.Axis
