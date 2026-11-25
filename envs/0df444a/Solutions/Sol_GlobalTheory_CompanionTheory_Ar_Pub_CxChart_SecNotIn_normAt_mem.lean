-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Pub.CxChart.SecNotIn.normAt_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:05:50.123502+00:00
-- url     : https://prove2.me/submissions/f90c5b5c-fd27-4ca3-8ba8-89b832b7a8c0

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
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartProjObjects
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MemChartComponents
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChartSectionNotMemComponents
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxChart_SecNotIn_eval_scale_eq_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxChart_SecNotIn_entry_ne_zero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartLift_segre_apply_6eeb1c8817f9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Pub GlobalTheory.CompanionTheory.Ar.Pub.CxChart
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
open ReciprocityTheory.AnForm.R (conePts)
open GroundTheory.Heights₂.Heights (chartLift chartLift_segre_apply)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart.SecNotIn
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart.SecNotIn
theorem _root_.solution {Q : Ideal (MRingOver ℂ ι)} (hQ : IsMultiHomogIdeal Q)
    {i : (k : K) → ι k} {x : (Σ k, ι k) → ℂ} (hx : ∀ f ∈ Q, eval x f = 0) (h : segre x i ≠ 0) :
    normAt i x ∈ conePts Q :=
  ⟨fun k => ⟨i k, mul_ne_zero (inv_ne_zero (entry_ne_zero h k)) (entry_ne_zero h k)⟩,
    eval_scale_eq_zero hQ (fun k => (x ⟨k, i k⟩)⁻¹) hx⟩
end GlobalTheory.CompanionTheory.Ar.Pub.CxChart.SecNotIn
