-- Prove2me | solution 1 for GlobalTheory.LevZeroUp.upZero_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:31.704249+00:00
-- url     : https://prove2.me/submissions/ca4e0482-4233-4c77-9273-7f6a5244a998

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UpZeroMemLev
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LevelZeroUniformizerFrameUnipotentAndEmbedGL
import Theorems.Thm_GlobalTheory_LevZeroUp_bas_val
import Theorems.Thm_GlobalTheory_LevZeroUp_bas_inv_val
import Theorems.Thm_GlobalTheory_LevZeroGen_upZero_apply
import Theorems.Thm_GlobalTheory_StepData_reGL_val


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
theorem _root_.solution (x : GL (Fin κ ⊕ Fin (s + 1)) k) (r c : XIx (Fin κ) t 0 ⊕ Fin (s + 1)) :
    (upZero S t x).val r c = scal t S.ϖ r * x.val (back t r) (back t c) * (scal t S.ϖ c)⁻¹ := by
  rw [upZero_apply, Units.val_mul, Units.val_mul, bas_val, bas_inv_val, mul_diagonal, diagonal_mul, reGL_val, reGL_val]
  rfl
end GlobalTheory.LevZeroUp
