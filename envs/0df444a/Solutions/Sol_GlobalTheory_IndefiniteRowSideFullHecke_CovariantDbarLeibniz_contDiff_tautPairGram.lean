-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz.contDiff_tautPairGram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:48:00.972806+00:00
-- url     : https://prove2.me/submissions/0aa3fd78-fd16-43ef-ba19-f816b92c9cfb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CovariantDbarLeibniz
import Theorems.Thm_GlobalTheory_IsPshC2On_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (a b : Unit ⊕ Unit) :
    ContDiff ℝ ∞ fun x => tautPairGram x a b := by
  have hc : ContDiff ℝ ∞ fun x : ℂ => conj x := conjCLE.contDiff
  rcases a with a | a <;> rcases b with b | b
  · exact contDiff_const.add (contDiff_id.mul hc)
  · exact contDiff_id
  · exact hc
  · exact contDiff_const
end GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz
