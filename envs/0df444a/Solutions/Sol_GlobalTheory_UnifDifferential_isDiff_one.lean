-- Prove2me | solution 1 for GlobalTheory.UnifDifferential.isDiff_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:48:19.514051+00:00
-- url     : https://prove2.me/submissions/240f22a7-2d0a-4aa0-a2d4-e6507fc1810e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubsingletonPrimeSpectrum
import Theorems.Thm_GlobalTheory_UnifDifferential_pullFn_comp
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_SqZero_scaleD_eq
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
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (sp IsTan fstD scaleD prodPts isTan_iff isLieComb_iff comp_one' isTan_mul isTan_one
  isTan_scale)
open GlobalTheory.SqZero
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.UnifDifferential
attribute [local instance] Over.cartesianMonoidalCategory
variable {K : Type} [Field K] {A : Over (Spec (CommRingCat.of K))} [GrpObj A]
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.UnifDifferential
theorem _root_.solution : u.IsDiff 0 (1 : epsR ℂ ⟶ A) := by
  intro U hU f
  rw [map_zero]
  refine (congrArg TrivSqZeroExt.snd
    (pullFn_comp (scaleD (0 : ℂ)) (1 : epsR ℂ ⟶ A) 1 (comp_one' _).symm U hU hU f)).trans ?_
  rw [scaleD_eq]
  simp [epsTo, dualTo_apply, Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl]
end GlobalTheory.UnifDifferential
