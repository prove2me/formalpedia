-- Prove2me | solution 1 for GlobalTheory.LevZeroUp.levelZeroOldIndexOfNew_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:22:30.542826+00:00
-- url     : https://prove2.me/submissions/6111aee5-ef15-4e8d-b912-ce3ede433647

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UpZeroMemLev
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LevelZeroUniformizerFrameUnipotentAndEmbedGL
import Theorems.Thm_GlobalTheory_StepData_standardOrderExtendedBasis_apply_low_block


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
theorem _root_.solution (i : Fin (s + 1)) : back (κ := κ) t (.inr i) = .inr i := by
  unfold back
  rw [show (stdOrd (Fin κ) t 0 (s + 1) (Nat.zero_add _)).symm (.inr i) = .inl (.inr i) from
    (Equiv.symm_apply_eq _).2 (standardOrderExtendedBasis_apply_low_block (Fin κ) t (l := s + 1) 0 (s + 1) (Nat.zero_add _) i).symm]
  exact (Equiv.symm_apply_eq _).2 rfl
end GlobalTheory.LevZeroUp
