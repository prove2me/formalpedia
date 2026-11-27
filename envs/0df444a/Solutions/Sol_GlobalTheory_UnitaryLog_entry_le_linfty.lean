-- Prove2me | solution 1 for GlobalTheory.UnitaryLog.entry_le_linfty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:36:36.503598+00:00
-- url     : https://prove2.me/submissions/1d46d309-928f-4b4e-878c-2336214ad8f0

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
theorem _root_.solution {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖X i j‖ ≤ ‖X‖ := by
  have h : ‖X i j‖₊ ≤ ‖X‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact (Finset.single_le_sum (f := fun j => ‖X i j‖₊) (fun _ _ => bot_le) (Finset.mem_univ j)).trans
      (Finset.le_sup (f := fun i => ∑ j, ‖X i j‖₊) (Finset.mem_univ i))
  exact_mod_cast h
end GlobalTheory.UnitaryLog
