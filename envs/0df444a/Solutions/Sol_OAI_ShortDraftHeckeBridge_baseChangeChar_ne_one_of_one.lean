-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.baseChangeChar_ne_one_of_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:53:54.240158+00:00
-- url     : https://prove2.me/submissions/714fe676-a765-4db0-a6d8-28fe6689bdab

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftHeckeBridge_not_both_principal
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
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ = 1) :
    baseChangeChar χ ≠ 1 := by
  intro h
  apply not_both_principal χ
  constructor
  · simp [hχ]
  · exact h
end OAI.ShortDraftHeckeBridge
