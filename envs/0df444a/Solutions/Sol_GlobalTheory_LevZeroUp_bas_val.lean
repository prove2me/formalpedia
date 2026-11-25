-- Prove2me | solution 1 for GlobalTheory.LevZeroUp.bas_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:30:48.839531+00:00
-- url     : https://prove2.me/submissions/b50e6914-eeba-443d-a1ba-8947980e698a

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
theorem _root_.solution : ((S.T t).bas 0 (s + 1) (Nat.zero_add _)).val = diagonal (scal t S.ϖ) := by
  show (embA _ (SplitFlip.diagGL fun i : Fin (s + 1) => S.ϖ ^ (i.val + 1))).val = _
  simp only [embA, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk, SplitFlip.diagGL_val]
  rw [← diagonal_one, fromBlocks_diagonal]
  congr 1
end GlobalTheory.LevZeroUp
