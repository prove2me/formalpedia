-- Prove2me | solution 1 for GlobalTheory.LocRep.rep_of_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:12.727657+00:00
-- url     : https://prove2.me/submissions/dfe07062-3ce8-41be-80ac-22fd289777f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
import Theorems.Thm_GlobalTheory_LocRep_locallyIntegrable_rep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.LocRep
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ}
open MeasureTheory
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ}
namespace GlobalTheory.LocRep
namespace _root_.GlobalTheory.LocRep
theorem _root_.solution [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [BorelSpace G]
    [IsLocallyFiniteMeasure μ]
    (hloc : ∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖)
    {v : K} {φ : G → ℂ} (hφ : LocallyIntegrable φ μ)
    (h : ∀ C, IsCompact C → ∫ x in C, ι v x ∂μ = ∫ x in C, φ x ∂μ) : ι v =ᵐ[μ] φ := by
  have hv : LocallyIntegrable (ι v) μ := _root_.GlobalTheory.LocRep.locallyIntegrable_rep hloc v
  have hdiff : (ι v - φ) =ᵐ[μ] 0 := by
    refine ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero' (hv.sub hφ) fun C hC => ?_
    simp only [Pi.sub_apply]
    rw [integral_sub (hv.integrableOn_isCompact hC) (hφ.integrableOn_isCompact hC), h C hC, sub_self]
  filter_upwards [hdiff] with x hx
  simpa [sub_eq_zero] using hx
end _root_.GlobalTheory.LocRep
end GlobalTheory.LocRep
