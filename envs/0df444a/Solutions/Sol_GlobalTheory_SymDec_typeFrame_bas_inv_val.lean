-- Prove2me | solution 1 for GlobalTheory.SymDec.typeFrame_bas_inv_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:30:14.442735+00:00
-- url     : https://prove2.me/submissions/65faa6ab-29a3-4909-9629-502f9797adb4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TypeFrameConjugationDecomposition
import Theorems.Thm_GlobalTheory_SymDec_dg_ne_zero
import Theorems.Thm_GlobalTheory_SymDec_typeFrame_bas_val

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
theorem _root_.solution (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    ((typeFrame ϖ ord).bas⁻¹).val = diagonal fun r => (dg ϖ r)⁻¹ := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [typeFrame_bas_val, diagonal_mul_diagonal]
  rw [← diagonal_one]; congr 1; funext r; exact mul_inv_cancel₀ (dg_ne_zero ϖ r)
end GlobalTheory.SymDec
