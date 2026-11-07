-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.local_ramified_nine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:56:58.637429+00:00
-- url     : https://prove2.me/submissions/daacb915-4866-4acc-a735-0b65680b04b1

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Theorems.Thm_OAI_ShortDraftHeckeBridge_absNorm_ramified
import Theorems.Thm_OAI_ShortDraftHeckeBridge_norm_nine_fiber_ramified
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
    normFiberCoeff (baseChangeWeight χ) 9 = 0 := by
  classical
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) 9
  unfold normFiberCoeff
  apply Finset.sum_eq_zero
  intro I hI
  have hnorm : Ideal.absNorm I = 9 := hf.mem_toFinset.mp hI
  have hfactor : I ∈ {I : Ideal O | ∃ P : Ideal O,
      P ∈ (Ideal.span {(3 : ℤ)}).primesOver O ∧ I = P ^ 2} := by
    rw [← norm_nine_fiber_ramified]
    exact hnorm
  obtain ⟨P, hP, rfl⟩ := hfactor
  have : P.IsPrime := hP.1
  have : P.LiesOver (Ideal.span {(3 : ℤ)}) := hP.2
  have hPN : Ideal.absNorm P = 3 := absNorm_ramified P
  have hnotunit : ¬ IsUnit P := by
    intro hunit
    have htop : P = ⊤ := Ideal.isUnit_iff.mp hunit
    rw [htop, Ideal.absNorm_top] at hPN
    norm_num at hPN
  have hnot : ¬ Squarefree (P ^ 2) := by
    intro hsq
    apply hnotunit
    exact hsq P (by rw [pow_two])
  rw [baseChangeWeight, UniqueFactorizationMonoid.moebius_of_not_squarefree hnot]
  simp
end OAI.ShortDraftHeckeBridge
