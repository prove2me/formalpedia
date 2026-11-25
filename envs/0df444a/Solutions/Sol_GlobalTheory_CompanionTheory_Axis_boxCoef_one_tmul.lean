-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Axis.boxCoef_one_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:24:55.907816+00:00
-- url     : https://prove2.me/submissions/3677e278-0d32-4581-b02e-35376287b92e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductFirstCohomologyComparison

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
theorem _root_.solution (S : Sys A.left P) (T : (Bx P)ᵒᵖ) (b : (OSys A.hom S).obj (op T.unop.2)) :
    (Algebra.TensorProduct.productMap (algL S T) (algR S T)) ((1 : (OSys A.hom S).obj (op T.unop.1)) ⊗ₜ[R] b) =
      algR S T b :=
  (Algebra.TensorProduct.productMap_apply_tmul _ _ _ _).trans
    ((congrArg (· * algR S T b) (map_one (algL S T))).trans (one_mul _))
end GlobalTheory.CompanionTheory.Axis
