-- Prove2me | solution 1 for GlobalTheory.HermFrame.Model.secondForm_tautPairGram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:47:51.532329+00:00
-- url     : https://prove2.me/submissions/61bea491-0bb5-4f09-ad65-f5c09afa91d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CurvSubQuotTautPairGram
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.HermFrame.Model
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
  {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}
namespace GlobalTheory.HermFrame.Model
theorem _root_.solution (ξ : ℂ) : secondForm tautPairGram 0 ξ = of fun _ _ => ξ := by
  have h : tautPairGram 0 = 1 := by
    rw [← fromBlocks_one]; ext (a | a) (b | b) <;> simp [tautPairGram]
  ext a b
  rw [secondForm_eq, conn, h, transpose_one, inv_one, Matrix.one_mul]
  change del (fun x : ℂ => x) 0 ξ = ξ
  rw [del_eq_fderiv differentiableAt_fun_id]; simp
end GlobalTheory.HermFrame.Model
