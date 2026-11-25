-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Pub.CxChart.SecNotIn.eval_scale_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:44:28.506624+00:00
-- url     : https://prove2.me/submissions/acaef3da-ad9b-4ad1-8fab-c1b6cecfd159

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartLift_segre_apply_6eeb1c8817f9
import Theorems.Thm_ReciprocityTheory_AnForm_R_aeval_smul_of_isMultiHomog


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
    (c : K → ℂ) {x : (Σ k, ι k) → ℂ} (hx : ∀ f ∈ Q, eval x f = 0) :
    ∀ f ∈ Q, eval (fun q => c q.1 * x q) f = 0 := by
  obtain ⟨S, hS, rfl⟩ := hQ
  have hle : Ideal.span S ≤ RingHom.ker (eval (fun q : Σ k, ι k => c q.1 * x q)) := by
    rw [Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    have h := ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog ha c x
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have h' : eval (fun q : Σ k, ι k => c q.1 * x q) f = (∏ k, c k ^ a k) * eval x f := h
    rw [h', hx f (Ideal.subset_span hf), mul_zero]
  exact fun f hf => hle hf
end GlobalTheory.CompanionTheory.Ar.Pub.CxChart.SecNotIn
