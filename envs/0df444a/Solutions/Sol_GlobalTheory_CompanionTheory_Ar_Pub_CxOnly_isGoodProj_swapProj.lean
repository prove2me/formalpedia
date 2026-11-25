-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Pub.CxOnly.isGoodProj_swapProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:25:16.595167+00:00
-- url     : https://prove2.me/submissions/b9f236ff-fda0-424d-8b0c-aaa2bfcbe3a9

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__PoincareLelong_e61d89ea90cf58ae
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__SheetDensityEqSetSheetDensity_cb85824e9bfdd8ba
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_CxPosDens
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_CxSimple
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SetFibreFiniteOfGoodProj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCriticalFibreInfinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_VolumeNonsimpleFibresEqZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_differentiableAt_proj_segre_36c3e8284232
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_differentiableAt_ratio_f91644499ea4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_inv_smul_eq_cons_954153cdf7f0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_not_injective_of_coord_eventually_const_10457ccc6c95
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_ratio_smul_cons_60856f0cf16b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_segre_scaleBlock_71f3a993f711
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_swapProj_apply_8d95c3de703d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Pub GlobalTheory.CompanionTheory.Ar.Pub.CxOnly
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GroundTheory.Heights₂.Heights.PtsSheetOnlyNull (ratio inv_smul_eq_cons ratio_smul_cons segre_scaleBlock
  differentiableAt_proj_segre differentiableAt_ratio swapProj swapProj_apply
  not_injective_of_coord_eventually_const)
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
namespace GlobalTheory.CompanionTheory.Ar.Pub.CxOnly
theorem _root_.solution {Q : Ideal (MRingOver ℂ ι)} {Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hΨ' : IsSetGoodProj (conePts Q) Ψ') (j : Fin (e + 1)) : IsSetGoodProj (conePts Q) (swapProj j Ψ') := by
  intro z hz h
  apply hΨ' z hz
  funext i
  have := congrFun h (Equiv.swap 0 j i)
  simpa [swapProj_apply] using this
end GlobalTheory.CompanionTheory.Ar.Pub.CxOnly
