-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz.homCovDel_leibniz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:51:54.206313+00:00
-- url     : https://prove2.me/submissions/36f5f71f-c9f5-4354-82fe-a70263ac4338

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CovariantDbarLeibniz
import Theorems.Thm_GlobalTheory_HermFrame_mdel_mul
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
theorem _root_.solution (A : E → Matrix m m ℂ) (B : E → Matrix l l ℂ) {T : E → Matrix l m ℂ}
    {S : E → Matrix m k ℂ} {z : E} (hT : MContDiffAt 1 T z) (hS : MContDiffAt 1 S z) (ξ : E) :
    mdel (fun x => T x * S x) z ξ + conn B z ξ * (T z * S z) =
      homCovDel A B T z ξ * S z + T z * (mdel S z ξ + conn A z ξ * S z) := by
  rw [mdel_mul hT hS, homCovDel]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
  abel
end GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz
