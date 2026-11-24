-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cutWeight_measurable_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:12:14.866539+00:00
-- url     : https://prove2.me/submissions/2dd5c9ab-836b-45c0-8175-4a4d9058fc32

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
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_DomCellLogNormMeasurableInvariant
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxChart_isClosed_domCell
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxChart_blockScale_mem_domCell
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxChart_measurable_absLogNorm
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxChart_absLogNorm_blockScale

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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)
namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart
theorem _root_.solution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ) (i : (k : K) → ι k),
    IsSmoothHerm A → (∀ k, A.a k = a k) → IsMultiHomog s a →
    Measurable ((domCell i).indicator (absLogNorm A s)) ∧
    ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      (domCell i).indicator (absLogNorm A s) (fun p => c p.1 * z p) =
        (domCell i).indicator (absLogNorm A s) z := by
  intro K _ ι _ A s a i hA hAa hs
  refine ⟨(measurable_absLogNorm A hA s).indicator (isClosed_domCell i).measurableSet, ?_⟩
  intro c z hc
  by_cases hz : z ∈ domCell i
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((blockScale_mem_domCell hc z i).2 hz),
      absLogNorm_blockScale A hAa hs hc z]
  · rw [Set.indicator_of_notMem hz,
      Set.indicator_of_notMem (mt (blockScale_mem_domCell hc z i).1 hz)]
end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
