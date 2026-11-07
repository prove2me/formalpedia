-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.normFiber_eq_pair_of_prime_powers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:54:21.620687+00:00
-- url     : https://prove2.me/submissions/4b9af93e-5322-42f0-b135-3e0675c937f1

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Theorems.Thm_OAI_ShortDraftHeckeBridge_pairAF_mult
import Theorems.Thm_OAI_ShortDraftHeckeBridge_pairAF_eq_pairInverseCoeff
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
theorem _root_.solution
    {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hb : (toArithmeticFunction (normFiberCoeff weight)).IsMultiplicative)
    (hlocal : ∀ p k : ℕ, p.Prime →
      (toArithmeticFunction (normFiberCoeff weight)) (p ^ k) =
        pairAF χ ψ (p ^ k))
    (n : ℕ) (hn : n ≠ 0) :
    normFiberCoeff weight n = pairInverseCoeff χ ψ n := by
  have heq : toArithmeticFunction (normFiberCoeff weight) = pairAF χ ψ :=
    (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
      _ hb _ (pairAF_mult χ ψ)).2 hlocal
  have h := congrFun (congrArg DFunLike.coe heq) n
  calc
    normFiberCoeff weight n = (toArithmeticFunction (normFiberCoeff weight)) n := by
      simp [toArithmeticFunction, hn]
    _ = pairAF χ ψ n := h
    _ = pairInverseCoeff χ ψ n := pairAF_eq_pairInverseCoeff χ ψ n
end OAI.ShortDraftHeckeBridge
