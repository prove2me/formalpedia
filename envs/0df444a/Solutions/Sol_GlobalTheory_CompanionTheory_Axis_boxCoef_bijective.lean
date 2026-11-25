-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Axis.boxCoef_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:45:22.164801+00:00
-- url     : https://prove2.me/submissions/267bd67a-edd4-45d6-9c16-5edbe12fc174

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductFirstCohomologyComparison
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_bijective_tens

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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Axis
open CategoryTheory.Limits
variable {R : Type} [CommRing R] {A : Over (Sp R)} {P : Type} [SemilatticeInf P]
namespace GlobalTheory.CompanionTheory.Axis
theorem _root_.solution (S : Sys A.left P) (T : (Bx P)ᵒᵖ) : Function.Bijective ((boxCoef S).α T) :=
  bijective_tens A.hom A.hom (S.u T.unop.1) (S.u T.unop.2) ((boxSys S).u T.unop) rfl (A ⊗ A).hom inf_le_left inf_le_right
    ((boxCoef S).α T) fun b c ↦ Algebra.TensorProduct.productMap_apply_tmul (algL S T) (algR S T) b c
end GlobalTheory.CompanionTheory.Axis
