-- Prove2me | solution 1 for GlobalTheory.UnifLieBasis.isDiff_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:05:09.531802+00:00
-- url     : https://prove2.me/submissions/61055a25-fa8b-47c9-9cf0-cd194fb47d59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLaw
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLieBasisOfHolUnif
import Theorems.Thm_GlobalTheory_TangentOrigin_tangent_mem_iff
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.UnifLieBasis
open TangentOrigin
open ReciprocityTheory.ChartRestriction.G.Chart (JetR jetAug qD rD scaleD IsTan isTan_iff prodPts isLieComb_iff)
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.UnifLieBasis
theorem _root_.solution {w : Fin g → ℂ} {v : epsR ℂ ⟶ A} (hv : IsTan (R := ℂ) (G := A) v) (hd : u.IsDiff w v) (c : ℂ) :
    u.IsDiff (c • w) (Chart.spMap (scaleD c) ≫ v) := by
  intro U h' f
  have h0 := (tangent_mem_iff (u := u) ((isTan_iff _).1 (Chart.isTan_scale c hv)) U).1 h'
  have h := (tangent_mem_iff (u := u) ((isTan_iff _).1 hv) U).2 h0
  rw [map_smul, ← hd U h f]
  refine (congrArg TrivSqZeroExt.snd
    (evalPt_spMap_comp (scaleD c : DualNumber ℂ →+* DualNumber ℂ) v.left U h h' f)).trans ?_
  exact TrivSqZeroExt.snd_map _ _
end GlobalTheory.UnifLieBasis
