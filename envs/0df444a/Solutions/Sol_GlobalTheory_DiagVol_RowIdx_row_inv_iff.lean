-- Prove2me | solution 1 for GlobalTheory.DiagVol.RowIdx.row_inv_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:42:58.616087+00:00
-- url     : https://prove2.me/submissions/b4d02679-d211-4e85-9568-ddff6939f74a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLRowCongruence
import Theorems.Thm_GlobalTheory_DiagVol_RowIdx_row_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.DiagVol GlobalTheory.DiagVol.RowIdx
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.DiagVol.RowIdx
theorem _root_.solution {R : Type} [CommRing R] (M N : GL ι R) (t : ι) :
    (M⁻¹ * N).val t = (1 : Matrix ι ι R) t ↔ (M⁻¹).val t = (N⁻¹).val t := by
  constructor
  · intro h
    have e1 : (M⁻¹).val = (M⁻¹ * N).val * (N⁻¹).val := by simp [mul_assoc]
    rw [e1, row_mul, h, ← row_mul, one_mul]
  · intro h
    rw [Units.val_mul, row_mul, h, ← row_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
end GlobalTheory.DiagVol.RowIdx
