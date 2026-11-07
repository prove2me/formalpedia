-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.invCharAF_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:49:27.54211+00:00
-- url     : https://prove2.me/submissions/c5e89696-a94d-4fae-aebb-48cbb7931a43

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
theorem _root_.solution {q : ℕ} (χ : DirichletCharacter ℂ q)
    {n : ℕ} (hn : n ≠ 0) :
    invCharAF χ n = χ n * (ArithmeticFunction.moebius n : ℂ) := by
  change ((toArithmeticFunction (χ ·)).pmul
    (ArithmeticFunction.moebius : ArithmeticFunction ℂ)) n = _
  rw [ArithmeticFunction.pmul_apply]
  simp [toArithmeticFunction, hn]
end OAI.ShortDraftHeckeBridge
