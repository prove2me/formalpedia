-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.chiMinusThree_mod_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:13:36.679468+00:00
-- url     : https://prove2.me/submissions/b380a69a-20f6-4400-8373-022cad869e5b

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
theorem _root_.solution (n : ℕ) (h : n % 3 = 0) :
    chiMinusThree n = 0 := by
  have hc : (n : ZMod 3) = 0 := by
    calc
      (n : ZMod 3) = ((n % 3 : ℕ) : ZMod 3) := by simp
      _ = 0 := by rw [h]; simp
  change ((quadraticChar (ZMod 3) (n : ZMod 3) : ℤ) : ℂ) = 0
  rw [hc]
  simp
end OAI.ShortDraftHeckeBridge
