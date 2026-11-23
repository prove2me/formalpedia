-- Prove2me | solution 1 for GlobalTheory.Published.LogLine.isOpen_offDivisor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:21:50.93353+00:00
-- url     : https://prove2.me/submissions/fa0f6301-081e-4cb1-81d3-a3e1e6225646

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
theorem _root_.solution {U : Set (Fin n → ℂ)} (hU : IsOpen U) (S : Finset (Fin n)) :
    IsOpen (offDivisor U S) := by
  have : offDivisor U S = U ∩ ⋂ i ∈ S, {z | z i ≠ 0} := by
    ext z; simp [offDivisor]
  rw [this]
  exact hU.inter (isOpen_biInter_finset fun i _ => isOpen_ne_fun (continuous_apply i) continuous_const)
end GlobalTheory.Published.LogLine
