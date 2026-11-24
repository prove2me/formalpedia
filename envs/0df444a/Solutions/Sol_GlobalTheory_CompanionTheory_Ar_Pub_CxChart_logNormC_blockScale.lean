-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Pub.CxChart.logNormC_blockScale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:37:07.603827+00:00
-- url     : https://prove2.me/submissions/2b7e703a-b5c2-4a08-97a1-b34610d46cc1

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
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxChart_eval_blockScale

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
theorem _root_.solution (A : HermLine ι) {s : MRingOver ℂ ι} {a : K → ℕ}
    (hA : ∀ k, A.a k = a k) (hs : IsMultiHomog s a) {c : K → ℂ} (hc : ∀ k, c k ≠ 0)
    (z : (Σ k, ι k) → ℂ) : logNormC A s (fun p => c p.1 * z p) = logNormC A s z := by
  unfold logNormC
  rw [eval_blockScale hs c z]
  have hh : A.h (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ A.a k) * A.h z := A.smul c z hc
  have hpos : 0 < ∏ k, ‖c k‖ ^ A.a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _
  have hn : ‖∏ k, c k ^ a k‖ = ∏ k, ‖c k‖ ^ A.a k := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_pow, hA k, zpow_natCast]
  rw [hh, norm_mul, hn, mul_div_mul_left _ _ hpos.ne']
end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
