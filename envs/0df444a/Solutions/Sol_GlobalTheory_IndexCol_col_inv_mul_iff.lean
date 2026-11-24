-- Prove2me | solution 1 for GlobalTheory.IndexCol.col_inv_mul_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:19:56.916414+00:00
-- url     : https://prove2.me/submissions/be030723-044e-4db3-bcc2-a4b2682bf33e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLColumnCongruence
import Theorems.Thm_GlobalTheory_IndexCol_val_sum_mul_lt_one

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
open GlobalTheory GlobalTheory.IndexCol
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.IndexCol
theorem _root_.solution {x : GL ι k} (hx : x ∈ KO k ι) (y : GL ι k) (t : ι) :
    (∀ s, valuation k (((x⁻¹ * y).val - 1) s t) < 1) ↔ ∀ s, valuation k ((y.val - x.val) s t) < 1 := by
  obtain ⟨hx1, hx2⟩ := (mem_KO_iff x).1 hx
  have e1 : (x⁻¹ * y).val - 1 = (x⁻¹).val * (y.val - x.val) := by
    rw [Units.val_mul, mul_sub, Units.inv_mul]
  have e2 : y.val - x.val = x.val * ((x⁻¹ * y).val - 1) := by
    rw [Units.val_mul, mul_sub, ← mul_assoc, Units.mul_inv, one_mul, mul_one]
  constructor
  · intro h s
    rw [e2, Matrix.mul_apply]
    exact val_sum_mul_lt_one _ _ (fun j => hx1 s j) h
  · intro h s
    rw [e1, Matrix.mul_apply]
    exact val_sum_mul_lt_one _ _ (fun j => hx2 s j) h
end GlobalTheory.IndexCol
