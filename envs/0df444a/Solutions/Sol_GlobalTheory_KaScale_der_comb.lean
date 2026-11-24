-- Prove2me | solution 1 for GlobalTheory.KaScale.der_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:32:51.662076+00:00
-- url     : https://prove2.me/submissions/20dfaba2-24ee-4848-ac60-21ecf5dc3843

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
import Theorems.Thm_GlobalTheory_KaScale_der_scale
import Theorems.Thm_GlobalTheory_KaScale_der_prod
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
variable [GrpObj A]
namespace GlobalTheory.KaScale
theorem _root_.solution {n : ℕ} {c : Fin n → K} {v : Fin n → (epsR K ⟶ A)} {w : epsR K ⟶ A}
    (hv : ∀ i, IsTangent (v i)) (hw : IsLieComb c v w) (U : A.left.Opens) (f : Γ(A.left, U)) :
    der w U f = ∑ i, c i * der (v i) U f := by
  rw [(isLieComb_iff c v w).1 hw]
  refine (der_prod U f _ (fun i => isTan_scale (c i) ((isTan_iff _).2 (hv i)))).2.trans ?_
  exact Finset.sum_congr rfl fun i _ => der_scale _ _ _ _
end GlobalTheory.KaScale
