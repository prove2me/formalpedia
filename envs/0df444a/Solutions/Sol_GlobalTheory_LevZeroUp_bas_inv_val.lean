-- Prove2me | solution 1 for GlobalTheory.LevZeroUp.bas_inv_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:37:21.275183+00:00
-- url     : https://prove2.me/submissions/ac2a1811-e8f9-4114-b318-3745c3e6445d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UpZeroMemLev
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LevelZeroUniformizerFrameUnipotentAndEmbedGL
import Theorems.Thm_GlobalTheory_LevZeroUp_scal_ne_zero
import Theorems.Thm_GlobalTheory_LevZeroUp_bas_val

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
theorem _root_.solution : (((S.T t).bas 0 (s + 1) (Nat.zero_add _))⁻¹).val = diagonal fun r => (scal t S.ϖ r)⁻¹ := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [bas_val, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext r; exact mul_inv_cancel₀ (scal_ne_zero t S.ϖ r)
end GlobalTheory.LevZeroUp
