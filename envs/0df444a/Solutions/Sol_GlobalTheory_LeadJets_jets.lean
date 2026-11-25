-- Prove2me | solution 1 for GlobalTheory.LeadJets.jets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:03:26.928607+00:00
-- url     : https://prove2.me/submissions/6c8f75e0-febe-4435-95fe-0f7e0760a73f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_TaylorExpansionLocalCoordinates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_NmatZeroMemBor
import Theorems.Thm_GlobalTheory_LeadJets_leadVal_diffOn
import Theorems.Thm_GlobalTheory_LeadJets_step

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
variable {n δ m : ℕ} {U : Fin m → Set (V n)} {f w : Fin m → V n → ℂ}
  {s : Fin m → V n → Fin n → ℂ} {t : Fin m → V n → Fin δ → ℂ}
namespace GlobalTheory.LeadJets
theorem _root_.solution {T a0 : ℕ} (ha0 : a0 ≤ T + 1)
    (hU : ∀ j, IsOpen (U j)) (h0 : ∀ j, (0 : V n) ∈ U j)
    (hf : ∀ j, DifferentiableOn ℂ (f j) (U j)) (hw : ∀ j, DifferentiableOn ℂ (w j) (U j))
    (hs : ∀ j k, DifferentiableOn ℂ (fun z => s j z k) (U j))
    (ht : ∀ j k, DifferentiableOn ℂ (fun z => t j z k) (U j))
    (hw0 : ∀ j, w j 0 ≠ 0) (hs0 : ∀ j k, s j 0 k = 0)
    (hcoord : ∀ j, (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => s j z k / w j z : V n)) 0).det ≠ 0)
    (hsurj : ∀ v : Fin m → ℂ, ∃ c : Fin δ → ℂ, ∀ j, ∑ k, c k * t j 0 k = v j) :
    ∃ cc : (Fin n → ℕ) → Fin δ → ℂ, ∀ j,
      (fun z => f j z - leadVal (s j z) (w j z) (t j z) T a0 cc) =O[𝓝 0] fun z => ‖z‖ ^ a0 := by
  have key : ∀ a ≤ a0, ∃ cc : (Fin n → ℕ) → Fin δ → ℂ, ∀ j,
      (fun z => f j z - leadVal (s j z) (w j z) (t j z) T a0 cc) =O[𝓝 0] fun z => ‖z‖ ^ a := by
    intro a
    induction a with
    | zero =>
      intro _
      refine ⟨0, fun j => ?_⟩
      have hc := (((hf j).sub (leadVal_diffOn (hs j) (hw j) (ht j) T a0 0)).differentiableAt
        ((hU j).mem_nhds (h0 j))).continuousAt
      exact (hc.tendsto.isBigO_one ℝ).congr_right fun v => (pow_zero _).symm
    | succ a ih =>
      intro ha
      obtain ⟨cc, hcc⟩ := ih (by omega)
      exact step (by omega) ha0 hU h0 hf hw hs ht hw0 hs0 hcoord hsurj cc hcc
  exact key a0 le_rfl
end GlobalTheory.LeadJets
