-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.chiMinusThree_mod_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:13:05.556295+00:00
-- url     : https://prove2.me/submissions/0072f158-2aa7-4b2e-8045-ba5954e93c1e

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
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
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution (n : ℕ) (h : n % 3 = 1) :
    chiMinusThree n = 1 := by
  have hc : (n : ZMod 3) = 1 := by
    calc
      (n : ZMod 3) = ((n % 3 : ℕ) : ZMod 3) := by simp
      _ = 1 := by rw [h]; simp
  change ((quadraticChar (ZMod 3) (n : ZMod 3) : ℤ) : ℂ) = 1
  rw [hc]
  simp
end OAI.ShortDraftHeckeBridge
