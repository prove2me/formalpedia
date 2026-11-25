-- Prove2me | solution 1 for GlobalTheory.KeyKa.KosBasis.phi_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:49:43.867905+00:00
-- url     : https://prove2.me/submissions/3abbad75-38f3-4e85-bf51-554d92ec5adf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KoszulExactOfGradedRegularStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KoszulExactOfRegular
import Theorems.Thm_GlobalTheory_KeyKa_KosBasis_phi_add
import Theorems.Thm_GlobalTheory_KeyKa_KosBasis_phi_zero
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KosBasis
variable {K : Type} [CommRing K]
namespace GlobalTheory.KeyKa.KosBasis
theorem _root_.solution (x : KeyIn K) {l N : ℕ} (b : Fin N → RR x l) {A : Type} (S : Finset A)
    (v : A → Fin N → K) (c) : phi x b (∑ i ∈ S, v i) c = ∑ i ∈ S, phi x b (v i) c := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, phi_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, phi_add, ih]
end GlobalTheory.KeyKa.KosBasis
