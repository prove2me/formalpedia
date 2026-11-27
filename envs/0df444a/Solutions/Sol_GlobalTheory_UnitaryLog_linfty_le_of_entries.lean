-- Prove2me | solution 1 for GlobalTheory.UnitaryLog.linfty_le_of_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:36:52.838351+00:00
-- url     : https://prove2.me/submissions/d83c1f47-b3bb-43f5-ba82-dd64dfb70c9e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsLogNearOneUnitaryGroupOfFormLinearBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open GlobalTheory GlobalTheory.UnitaryLog
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace GlobalTheory.UnitaryLog
theorem _root_.solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ i j, ‖M i j‖ ≤ δ) : ‖M‖ ≤ n * δ := by
  have h' : ‖M‖₊ ≤ (n : NNReal) * δ.toNNReal := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun i _ => ?_
    calc ∑ j, ‖M i j‖₊ ≤ ∑ _j : Fin n, δ.toNNReal :=
          Finset.sum_le_sum fun j _ => by
            rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hδ]; exact h i j
      _ = (n : NNReal) * δ.toNNReal := by simp
  have := NNReal.coe_le_coe.2 h'
  simpa [Real.coe_toNNReal _ hδ] using this
end GlobalTheory.UnitaryLog
