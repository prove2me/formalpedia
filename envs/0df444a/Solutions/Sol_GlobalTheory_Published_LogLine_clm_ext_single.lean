-- Prove2me | solution 1 for GlobalTheory.Published.LogLine.clm_ext_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:39:59.76005+00:00
-- url     : https://prove2.me/submissions/a3a0f9a3-3645-4f22-a9a6-ee2de9397df0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__ExistsHorizontalGeneratorOfCharts_f0ad16e2bc421ec8

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
theorem _root_.solution {L M : (Fin n → ℂ) →L[ℂ] ℂ}
    (h : ∀ i, L (Pi.single i 1) = M (Pi.single i 1)) : L = M := by
  ext v
  rw [← Finset.univ_sum_single v, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (v i) : Fin n → ℂ) = v i • (Pi.single i 1 : Fin n → ℂ) := by
    rw [← Pi.single_smul]; simp
  rw [this, map_smul, map_smul, h i]
end GlobalTheory.Published.LogLine
