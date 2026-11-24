-- Prove2me | solution 1 for GlobalTheory.KaScale.der_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:57:37.599076+00:00
-- url     : https://prove2.me/submissions/263103ab-c335-4f80-a7a5-db2ca591cb56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KaFormHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubsingletonPrimeSpectrum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsSquareDetComparisonScaleSec
import Theorems.Thm_GlobalTheory_KaScale_der_pos
import Theorems.Thm_GlobalTheory_KaScale_der_neg
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_SqZero_scaleD_eq
import Theorems.Thm_GlobalTheory_UnifDifferential_le_preimage_comp
import Theorems.Thm_GlobalTheory_UnifDifferential_le_preimage_of_comp
import Theorems.Thm_GlobalTheory_UnifDifferential_pullFn_comp
import Theorems.Thm_GlobalTheory_UnifDifferential_subsingleton_primeSpectrum
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open ReciprocityTheory.ChartRestriction.G.Chart (sp fstD scaleD prodPts isTan_iff isLieComb_iff comp_one' isTan_mul isTan_one
  isTan_scale)
open GlobalTheory.UnifDifferential GlobalTheory.SqZero
noncomputable section
open GlobalTheory GlobalTheory.KaScale
variable {K : Type} [Field K] {A : Over (Spec (CommRingCat.of K))}
namespace GlobalTheory.KaScale
theorem _root_.solution (v : sp (R₀ := K) (DualNumber K) ⟶ A) (c : K) (U : A.left.Opens) (f : Γ(A.left, U)) :
    der (Chart.spMap (scaleD c) ≫ v) U f = c * der v U f := by
  have : Subsingleton (PrimeSpectrum (DualNumber K)) := subsingleton_primeSpectrum K K
  by_cases h : ⊤ ≤ v.left ⁻¹ᵁ U
  · have h' := le_preimage_comp (scaleD c) v _ rfl U h
    rw [der_pos _ _ _ h, der_pos _ _ _ h', pullFn_comp (scaleD c) v _ rfl U h h' f, scaleD_eq]
    simp [epsTo, dualTo_apply, Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl, mul_comm]
  · rw [der_neg _ _ _ h, der_neg _ _ _ (fun h' => h (le_preimage_of_comp (scaleD c) v _ rfl U h')), mul_zero]
end GlobalTheory.KaScale
