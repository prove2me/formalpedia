-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.local_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:54:43.4655+00:00
-- url     : https://prove2.me/submissions/e568e248-ed35-4fc8-a892-5b693a93d9b3

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
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
theorem _root_.solution {q : ℕ} (χ : DirichletCharacter ℂ q) :
    normFiberCoeff (baseChangeWeight χ) 1 = 1 := by
  classical
  have hfinset : (Ideal.finite_setOfPred_absNorm_eq (S := O) 1).toFinset = {⊤} := by
    ext I
    simp only [Set.Finite.mem_toFinset, Finset.mem_singleton]
    exact Ideal.absNorm_eq_one_iff
  unfold normFiberCoeff
  rw [hfinset]
  simp only [Finset.sum_singleton]
  change baseChangeWeight χ ⊤ = 1
  have hunit : IsUnit (⊤ : Ideal O) := Ideal.isUnit_iff.mpr rfl
  have hmu : UniqueFactorizationMonoid.moebius (⊤ : Ideal O) = 1 := hunit.moebius_eq
  change (UniqueFactorizationMonoid.moebius (⊤ : Ideal O) : ℂ) *
    χ (Ideal.absNorm (⊤ : Ideal O)) = 1
  rw [hmu, Ideal.absNorm_top]
  simp
end OAI.ShortDraftHeckeBridge
