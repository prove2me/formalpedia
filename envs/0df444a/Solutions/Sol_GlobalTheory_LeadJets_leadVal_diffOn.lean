-- Prove2me | solution 1 for GlobalTheory.LeadJets.leadVal_diffOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:32:31.659906+00:00
-- url     : https://prove2.me/submissions/1853bce3-4c27-438b-a76a-9e47a77f9166

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_TaylorExpansionLocalCoordinates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_NmatZeroMemBor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open Filter Asymptotics
open GlobalTheory GlobalTheory.LeadJets
noncomputable section
namespace GlobalTheory.LeadJets
theorem _root_.solution {n δ : ℕ} {U : Set (V n)} {s : V n → Fin n → ℂ} {w : V n → ℂ}
    {t : V n → Fin δ → ℂ} (hs : ∀ k, DifferentiableOn ℂ (fun z => s z k) U)
    (hw : DifferentiableOn ℂ w U) (ht : ∀ k, DifferentiableOn ℂ (fun z => t z k) U)
    (T a0 : ℕ) (cc : (Fin n → ℕ) → Fin δ → ℂ) :
    DifferentiableOn ℂ (fun z => leadVal (s z) (w z) (t z) T a0 cc) U := by
  unfold leadVal
  refine DifferentiableOn.fun_sum fun α _ => DifferentiableOn.fun_sum fun k _ => ?_
  refine (((differentiableOn_const _).mul ?_).mul (hw.pow _)).mul (ht k)
  refine Finset.induction_on (motive := fun F : Finset (Fin n) =>
    DifferentiableOn ℂ (fun z => ∏ q ∈ F, s z q ^ α q) U) Finset.univ ?_ fun q F hq ih => ?_
  · simpa using differentiableOn_const (1 : ℂ)
  · simp only [Finset.prod_insert hq]
    exact ((hs q).fun_pow _).mul ih
end GlobalTheory.LeadJets
