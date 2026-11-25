-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz.lorentzPairGram_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:54:45.594292+00:00
-- url     : https://prove2.me/submissions/56773ef7-5cc6-4533-9f3d-93d46112db17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CovariantDbarLeibniz
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_sub
import Theorems.Thm_GlobalTheory_HermFrame_IsPosFrame_sub
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
theorem _root_.solution : IsHermFrame (Metric.ball 0 1) lorentzPairGram ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1, IsUnit (subField lorentzPairGram z).det) ∧
    ¬ (lorentzPairGram 0).PosDef := by
  have hc : ContDiff ℝ ∞ fun x : ℂ => conj x := conjCLE.contDiff
  have hs : ∀ z ∈ Metric.ball (0 : ℂ) 1, (1 - z * conj z) ≠ 0 := fun z hz h => by
    have h1 : ‖z‖ < 1 := by simpa using hz
    rw [mul_conj', sub_eq_zero] at h
    have h2 : (1 : ℝ) = ‖z‖ ^ 2 := by exact_mod_cast h
    nlinarith [norm_nonneg z]
  refine ⟨⟨Metric.isOpen_ball, fun a b => ContDiff.contDiffOn ?_, fun z _ => ?_, fun z _ => ?_⟩,
    fun z hz => ?_, fun h => ?_⟩
  · rcases a with a | a <;> rcases b with b | b
    · exact contDiff_const.sub (contDiff_id.mul hc)
    · exact contDiff_id.neg
    · exact hc.neg
    · exact contDiff_const
  · ext (a | a) (b | b) <;> simp [lorentzPairGram, mul_comm]
  · let P : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ := fromBlocks 1 (of fun _ _ => z) 0 1
    let Q : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ := fromBlocks 1 0 (of fun _ _ => -conj z) (-1)
    have e : lorentzPairGram z = P * Q := by
      ext (a | a) (b | b) <;> simp [lorentzPairGram, P, Q, mul_apply, sub_eq_add_neg]
    rw [e, det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂]
    simp
  · rw [det_unique]; exact (hs z hz).isUnit
  · have := h.diag_pos (i := Sum.inr ())
    simp [lorentzPairGram] at this
    exact absurd this (by norm_num)
end GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz
