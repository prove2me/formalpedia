-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.pair_zero_free_of_normFiber_exp_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:54:36.586896+00:00
-- url     : https://prove2.me/submissions/555cea6d-a574-4fa6-a196-691bbd9a8513

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberMellin_analytic
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberMellin_eq_LSeries
import Theorems.Thm_OAI_ShortDraftHeckeBridge_pair_zero_free_of_normFiber_continuation


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
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (hexp : ∀ t : ℝ, 0 < t → Summable
      (fun n : ℕ => normFiberCoeff weight n * Real.exp (-(n : ℝ) * t)))
    (σ : ℝ) (hσpos : 0 < σ) (hσ : σ < 1)
    (hlocal : LocallyIntegrableOn
      (fun D : ℝ => normFiberExpSum weight D⁻¹) (Set.Ioi 0))
    (htop : (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (hflat : ∀ b : ℝ,
      (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[𝓝[>] (0 : ℝ)]
        (fun D : ℝ => D ^ b))
    (ρ : ℂ) (hρ : σ < ρ.re) :
    χ.LFunction ρ ≠ 0 ∧ ψ.LFunction ρ ≠ 0 := by
  exact pair_zero_free_of_normFiber_continuation χ ψ hχ hψ weight hcoeff
    σ hσ (normFiberMellin weight)
    (normFiberMellin_analytic weight σ hσpos hlocal htop hflat)
    (fun s hs => normFiberMellin_eq_LSeries χ ψ weight hcoeff ha0 hexp s hs)
    ρ hρ
end OAI.ShortDraftHeckeBridge
