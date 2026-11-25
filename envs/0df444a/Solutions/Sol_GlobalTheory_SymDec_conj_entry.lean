-- Prove2me | solution 1 for GlobalTheory.SymDec.conj_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:42:00.965193+00:00
-- url     : https://prove2.me/submissions/a7ef210f-03d0-4bdf-af92-f4e53ad44494

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TypeFrameConjugationDecomposition
import Theorems.Thm_GlobalTheory_SymDec_typeFrame_bas_val
import Theorems.Thm_GlobalTheory_SymDec_typeFrame_bas_inv_val
import Theorems.Thm_GlobalTheory_StepData_LatFrame_conj_apply
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
noncomputable section
open GlobalTheory GlobalTheory.SymDec
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
variable {k : Type} [Field k] {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.SymDec
theorem _root_.solution [Fintype ι] [DecidableEq ι] (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) (g : GL ι k) (r s : n ⊕ Fin c) :
    ((typeFrame ϖ ord).conj g).val r s = dg ϖ r * g.val (ord.symm r) (ord.symm s) * (dg ϖ s)⁻¹ := by
  rw [LatFrame.conj_apply, Units.val_mul, Units.val_mul, typeFrame_bas_inv_val, typeFrame_bas_val,
    mul_diagonal, diagonal_mul, reGL_val]
  rfl
end GlobalTheory.SymDec
