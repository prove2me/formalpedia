-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Axis.isPullO_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:59:55.299802+00:00
-- url     : https://prove2.me/submissions/92a93351-4085-4c6f-809a-48cbb99c0e32

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteSemilatticeSystemStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SmoothSectionsAffineFlatStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AbelianSchemeBaseChangeExistsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUniqueConstantOfCompatibleFamilyStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductFirstCohomologyComparisonStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsPullOWOverCompStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FlatCocycleTensorRepresentationStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CocycleTensorCoboundaryClassZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClassZeroCocycleTensorCoboundaryStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CocycleOnProductFromSecondFactorStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FirstCohomologyOfBaseZero
import Theorems.Thm_GlobalTheory_CechDR_existsUnique_isPullO


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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Axis
namespace GlobalTheory.CompanionTheory.Axis
theorem _root_.solution {R : Type} [CommRing R] {X Y : Over (Sp R)} (f : X ⟶ Y) {a : HO1 Y.hom} {b b' : HO1 X.hom}
    (h : IsPullO (wOver f) a b) (h' : IsPullO (wOver f) a b') : b = b' :=
  (existsUnique_isPullO (wOver f) a).unique h h'
end GlobalTheory.CompanionTheory.Axis
