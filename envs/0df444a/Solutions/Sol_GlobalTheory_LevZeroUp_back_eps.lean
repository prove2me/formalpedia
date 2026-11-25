-- Prove2me | solution 1 for GlobalTheory.LevZeroUp.back_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:38:08.326166+00:00
-- url     : https://prove2.me/submissions/5ee1fecb-4787-49be-a020-34e0d7a10420

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UpZeroMemLev
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LevelZeroUniformizerFrameUnipotentAndEmbedGL

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
theorem _root_.solution (i : Fin κ) : back (s := s) t (.inl (.inl (.inl i))) = .inl i := by
  unfold back
  rw [show (stdOrd (Fin κ) t 0 (s + 1) (Nat.zero_add _)).symm (.inl (.inl (.inl i))) = .inl (.inl i) from
    (Equiv.symm_apply_eq _).2 rfl]
  exact (Equiv.symm_apply_eq _).2 rfl
end GlobalTheory.LevZeroUp
