-- Prove2me | solution 1 for GlobalTheory.LatticePartition.summable_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:40:00.760563+00:00
-- url     : https://prove2.me/submissions/0e84baaa-86a9-4d59-8292-c5a75fdc2495

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RealCompactPartitionUnity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff
noncomputable section
open GlobalTheory GlobalTheory.LatticePartition
namespace GlobalTheory.LatticePartition
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] :
    Summable fun z : L => ((1 + ‖z‖) ^ (Module.finrank ℤ L + 1))⁻¹ := by
  refine Summable.of_norm_bounded_eventually (ZLattice.summable_norm_pow_inv L _ (Nat.lt_succ_self _)) ?_
  refine (Set.finite_singleton (0 : L)).subset fun z hz => ?_
  by_contra h0
  apply hz
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 h0
  show ‖((1 + ‖z‖) ^ (Module.finrank ℤ L + 1))⁻¹‖ ≤ ‖z‖⁻¹ ^ (Module.finrank ℤ L + 1)
  rw [norm_inv, norm_pow, Real.norm_of_nonneg (by positivity), inv_pow]
  exact inv_anti₀ (pow_pos hz0 _) (pow_le_pow_left₀ hz0.le (by linarith) _)
end GlobalTheory.LatticePartition
