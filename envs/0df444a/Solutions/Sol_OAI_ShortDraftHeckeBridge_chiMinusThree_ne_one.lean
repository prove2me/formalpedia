-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.chiMinusThree_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:50:50.173902+00:00
-- url     : https://prove2.me/submissions/16685592-fb9f-4c51-a9fa-0810bf91798f

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Theorems.Thm_OAI_ShortDraftHeckeBridge_chiMinusThree_two

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution : chiMinusThree ≠ 1 := by
  intro h
  have hh := congrArg (fun ξ : DirichletCharacter ℂ 3 => ξ (2 : ℕ)) h
  rw [chiMinusThree_two] at hh
  have hunit : IsUnit (2 : ZMod 3) := by decide
  change (-1 : ℂ) = (1 : DirichletCharacter ℂ 3) (2 : ZMod 3) at hh
  rw [MulChar.one_apply hunit] at hh
  norm_num at hh
end OAI.ShortDraftHeckeBridge
