-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.chiMinusThree_mod_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:12:52.154865+00:00
-- url     : https://prove2.me/submissions/7183799b-9eca-4877-9826-2711fe8e5f3a

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftHeckeBridge_chiMinusThree_two
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
theorem _root_.solution (n : ℕ) (h : n % 3 = 2) :
    chiMinusThree n = -1 := by
  have hc : (n : ZMod 3) = 2 := by
    calc
      (n : ZMod 3) = ((n % 3 : ℕ) : ZMod 3) := by simp
      _ = 2 := by rw [h]; simp
  change ((quadraticChar (ZMod 3) (n : ZMod 3) : ℤ) : ℂ) = -1
  rw [hc]
  change chiMinusThree (2 : ℕ) = -1
  exact chiMinusThree_two
end OAI.ShortDraftHeckeBridge
