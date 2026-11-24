-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Pub.CxChart.measurable_absLogNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:20:29.773933+00:00
-- url     : https://prove2.me/submissions/e3fd1dfa-0d27-4fb4-827c-24644ce34f34

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isOpen_blockNonzero


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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart
theorem _root_.solution (A : HermLine ι) (hA : IsSmoothHerm A) (s : MRingOver ℂ ι) :
    Measurable (absLogNorm A s) := by
  classical
  set T : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hT
  have hTm : MeasurableSet T := isOpen_blockNonzero.measurableSet
  have hh : Measurable (T.piecewise A.h 1) :=
    hA.continuousOn.measurable_piecewise continuousOn_const hTm
  have heq : absLogNorm A s =
      T.piecewise (fun z => |Real.log (‖eval z s‖ / T.piecewise A.h 1 z)|) 0 := by
    funext z
    by_cases hz : z ∈ T
    · have hz' : ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0 := hz
      rw [Set.piecewise_eq_of_mem _ _ _ hz, Set.piecewise_eq_of_mem _ _ _ hz]
      simp only [absLogNorm, if_pos hz', logNormC]
    · have hz' : ¬ ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0 := hz
      rw [Set.piecewise_eq_of_notMem _ _ _ hz]
      simp only [absLogNorm, if_neg hz', Pi.zero_apply]
  rw [heq]
  refine Measurable.piecewise hTm ?_ measurable_const
  exact continuous_abs.measurable.comp
    (Real.measurable_log.comp ((MvPolynomial.continuous_eval s).norm.measurable.div hh))
end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
