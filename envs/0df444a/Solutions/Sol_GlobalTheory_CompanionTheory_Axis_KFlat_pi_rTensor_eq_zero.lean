-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Axis.KFlat.pi_rTensor_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:34:59.637741+00:00
-- url     : https://prove2.me/submissions/4b48febf-0516-4520-9d17-d19daac72964

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CocycleTensorCoboundaryClassZero
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_KFlat_piLeft_apply_eq

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Axis GlobalTheory.CompanionTheory.Axis.KFlat
variable {R : Type} [CommRing R] {J : Type} [Finite J] {M : J → Type} [∀ i, AddCommGroup (M i)]
  [∀ i, Module R (M i)] {N : Type} [AddCommGroup N] [Module R N]
namespace GlobalTheory.CompanionTheory.Axis.KFlat
theorem _root_.solution (w : (∀ i, M i) ⊗[R] N)
    (h : ∀ i, (LinearMap.proj i : (∀ i, M i) →ₗ[R] M i).rTensor N w = 0) : w = 0 := by
  classical
  have := Fintype.ofFinite J
  apply (TensorProduct.piLeft R N M).injective
  funext i
  rw [piLeft_apply_eq, h, map_zero]
  rfl
end GlobalTheory.CompanionTheory.Axis.KFlat
