-- Prove2me | solution 1 for GlobalTheory.LevZeroUp.simpleSum_upZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:09:46.588798+00:00
-- url     : https://prove2.me/submissions/c9d38a90-606c-4e29-817c-076dc3deded1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UpZeroMemLev
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LevelZeroUniformizerFrameUnipotentAndEmbedGL
import Theorems.Thm_GlobalTheory_LevZeroUp_levelZeroOldIndexOfNew_inr
import Theorems.Thm_GlobalTheory_LevZeroUp_upZero_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.LevZeroUp
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LevZeroGen GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
namespace GlobalTheory.LevZeroUp
theorem _root_.solution (n : GL (Fin κ ⊕ Fin (s + 1)) k) :
    simpleSum (upZero S t n) = ((S.ϖ⁻¹ : kˣ) : k) * simpleSum n := by
  have hϖ : (S.ϖ : k) ≠ 0 := S.ϖ.ne_zero
  unfold simpleSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [upZero_entry, levelZeroOldIndexOfNew_inr, levelZeroOldIndexOfNew_inr]
    simp only [scal, Sum.elim_inr, h, Units.val_inv_eq_inv_val]
    field_simp
    ring
  · simp
end GlobalTheory.LevZeroUp
