-- Prove2me | solution 2 for GlobalTheory.LocRep.locallyIntegrable_rep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:35.768862+00:00
-- url     : https://prove2.me/submissions/7a91ce65-f262-4106-baeb-589bceab51f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep

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
theorem _root_.solution [LocallyCompactSpace G]
    (hloc : ∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖) (v : K) :
    LocallyIntegrable (ι v) μ := by
  intro x
  obtain ⟨C, hC, hCx⟩ := exists_compact_mem_nhds x
  obtain ⟨M, hM⟩ := hloc C hC
  exact ⟨C, hCx, (hM v).1⟩
end _root_.GlobalTheory.LocRep
end GlobalTheory.LocRep
