-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz.isPosFrame_tautPairGram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:54:24.326104+00:00
-- url     : https://prove2.me/submissions/1b664cb4-8040-4a7d-988e-386dfac4a075

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CovariantDbarLeibniz
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CovariantDbarLeibniz_contDiff_tautPairGram
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_one
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
open Matrix Complex ComplexConjugate
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m l k : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
namespace GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz
theorem _root_.solution : IsPosFrame Set.univ tautPairGram := by
  refine ⟨isOpen_univ, fun a b => (contDiff_tautPairGram a b).contDiffOn, fun z _ => ?_⟩
  let P : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ := fromBlocks 1 (of fun _ _ => z) 0 1
  have hP : IsUnit P := by
    rw [isUnit_iff_isUnit_det, det_fromBlocks_zero₂₁]; simp
  have e : tautPairGram z = P * 1 * Pᴴ := by
    ext (a | a) (b | b) <;> simp [tautPairGram, P, mul_apply]
  rw [e]
  exact PosDef.one.mul_mul_conjTranspose_same (vecMul_injective_iff_isUnit.2 hP)
end GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz
