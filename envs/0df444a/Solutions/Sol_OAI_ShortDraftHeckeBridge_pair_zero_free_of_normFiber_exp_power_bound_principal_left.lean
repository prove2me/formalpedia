-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.pair_zero_free_of_normFiber_exp_power_bound_principal_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:56:43.971661+00:00
-- url     : https://prove2.me/submissions/ccf98efe-925c-40d5-89da-7f62a35009d7

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberMellin_analytic_of_coeff
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberMellin_eq_LSeries_of_coeff
import Theorems.Thm_OAI_ShortDraftHeckeBridge_pair_zero_free_of_normFiber_continuation_principal_left


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
theorem _root_.solution
    {q r : ℕ} [NeZero q] [NeZero r]
    (ψ : DirichletCharacter ℂ r) (hψ : ψ ≠ 1)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      normFiberCoeff weight n =
        pairInverseCoeff (1 : DirichletCharacter ℂ q) ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (σ : ℝ) (hσpos : 0 < σ) (hσ : σ < 1)
    (htop : (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ρ ≠ 0 ∧
      ψ.LFunction ρ ≠ 0 := by
  exact pair_zero_free_of_normFiber_continuation_principal_left ψ hψ
    weight hcoeff σ hσ (normFiberMellin weight)
    (normFiberMellin_analytic_of_coeff 1 ψ weight hcoeff ha0 σ hσpos htop)
    (fun s hs => normFiberMellin_eq_LSeries_of_coeff 1 ψ weight hcoeff ha0 s hs)
    ρ hρ hρone
end OAI.ShortDraftHeckeBridge
