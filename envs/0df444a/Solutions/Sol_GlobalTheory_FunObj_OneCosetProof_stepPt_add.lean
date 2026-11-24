-- Prove2me | solution 1 for GlobalTheory.FunObj.OneCosetProof.stepPt_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:51:04.926476+00:00
-- url     : https://prove2.me/submissions/71c529c5-5731-4587-8e22-3041a5579fe6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCosetOfIsTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.OneCosetProof
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type} [Field k]
namespace GlobalTheory.FunObj.OneCosetProof
theorem _root_.solution {n n' : Type} {c : ℕ} (x₀ : Matrix n n' k) (e : StepVar n c n' → k)
    (Y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (hY : ∀ r s, ¬ Free (c / 2 + 1) (r, s) → Y r s = 0) :
    stepPt x₀ (e + fun rs => Y rs.1.1 rs.1.2) = stepPt x₀ e + Y := by
  ext r s
  simp only [stepPt, Matrix.add_apply, Matrix.of_apply]
  by_cases h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s)
  · rw [dif_pos h, dif_pos h]
    simp only [Pi.add_apply]
    ring
  · rw [dif_neg h, dif_neg h, hY r s (fun hf => h (Or.inl hf))]
    simp
end GlobalTheory.FunObj.OneCosetProof
