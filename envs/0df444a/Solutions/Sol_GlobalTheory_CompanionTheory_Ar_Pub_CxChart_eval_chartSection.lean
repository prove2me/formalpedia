-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Pub.CxChart.eval_chartSection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:32:22.566368+00:00
-- url     : https://prove2.me/submissions/8bb83c55-f3cf-4b63-aacf-2da0cbb8ebf8

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
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MeasurableDomCellLogNormChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartLift_blockNonzero_4a49d0f77c5b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartWeight_of_coord_6d29224d3334
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_chartLift_8692f480c9b0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_segre_chartLift_cde5bc6f2110


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Pub GlobalTheory.CompanionTheory.Ar.Pub.CxChart
open GroundTheory.Heights₂.Heights (chartLift chartLiftDom contDiff_chartLift chartLift_blockNonzero segre_chartLift
  chartWeight_of_coord)
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {m : ℕ}
namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart
theorem _root_.solution (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (s : MRingOver ℂ ι)
    (x : Fin m → ℂ) : MvPolynomial.eval x (chartSection σ i s) = MvPolynomial.eval (chartLift σ i x) s := by
  induction s using MvPolynomial.induction_on with
  | C c => simp [chartSection]
  | add p q hp hq =>
    have : chartSection σ i (p + q) = chartSection σ i p + chartSection σ i q := by
      simp [chartSection]
    rw [this, map_add, map_add, hp, hq]
  | mul_X p q hp =>
    have : chartSection σ i (p * X q) =
        chartSection σ i p * X (σ.symm (Function.update i q.1 q.2)) := by
      simp [chartSection]
    rw [this, map_mul, map_mul, hp]
    simp [chartLift]
end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
