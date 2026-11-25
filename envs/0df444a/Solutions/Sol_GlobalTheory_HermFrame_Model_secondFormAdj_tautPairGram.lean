-- Prove2me | solution 1 for GlobalTheory.HermFrame.Model.secondFormAdj_tautPairGram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:53:33.005772+00:00
-- url     : https://prove2.me/submissions/1a953ab5-3b65-4a6b-b8d7-25011f6538ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CurvSubQuotTautPairGram
import Theorems.Thm_GlobalTheory_HermFrame_Model_secondForm_tautPairGram
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
theorem _root_.solution (η : ℂ) :
    secondFormAdj tautPairGram 0 η = of fun _ _ => conj η := by
  have h : tautPairGram 0 = 1 := by
    rw [← fromBlocks_one]; ext (a | a) (b | b) <;> simp [tautPairGram]
  have h1 : subGram (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ) = 1 := by
    rw [← fromBlocks_one]; rfl
  have h2 : quotGram (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ) = 1 := by
    have : toBlocks₂₁ (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ) = 0 := by
      rw [← fromBlocks_one]; rfl
    rw [quotGram, this, Matrix.zero_mul, Matrix.zero_mul, sub_zero, ← fromBlocks_one]; rfl
  rw [secondFormAdj, h, h1, h2, secondForm_tautPairGram]
  ext a b; simp [adj]
end GlobalTheory.HermFrame.Model
