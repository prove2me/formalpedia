-- Prove2me | solution 1 for GlobalTheory.Published.LogLine.eqOn_of_eqOn_offDivisor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:07.453972+00:00
-- url     : https://prove2.me/submissions/82ef2867-a3ad-4753-a166-16ba8b20895e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__ExistsHorizontalGeneratorOfCharts_f0ad16e2bc421ec8
import Theorems.Thm_GlobalTheory_Published_LogLine_offDivisor_subset
import Theorems.Thm_GlobalTheory_Published_LogLine_subset_closure_offDivisor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.LogLine
variable {n : ℕ}
namespace GlobalTheory.Published.LogLine
theorem _root_.solution {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (S : Finset (Fin n)) {F G : (Fin n → ℂ) → Y}
    (hF : ContinuousOn F U) (hG : ContinuousOn G U) (h : EqOn F G (offDivisor U S)) :
    EqOn F G U :=
  h.of_subset_closure hF hG (offDivisor_subset U S) (subset_closure_offDivisor hU S)
end GlobalTheory.Published.LogLine
