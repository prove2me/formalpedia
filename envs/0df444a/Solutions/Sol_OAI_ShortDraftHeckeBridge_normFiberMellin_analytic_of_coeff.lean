-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.normFiberMellin_analytic_of_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:55:33.182407+00:00
-- url     : https://prove2.me/submissions/3a8b510d-8d20-4066-ae0b-d1471b323327

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberExpSum_inv_locallyIntegrableOn_pos
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberExpSum_flat_at_zero
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberMellin_analytic

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
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (σ : ℝ) (hσpos : 0 < σ)
    (htop : (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ)) :
    AnalyticOnNhd ℂ (normFiberMellin weight) {s : ℂ | σ < s.re} :=
  normFiberMellin_analytic weight σ hσpos
    (normFiberExpSum_inv_locallyIntegrableOn_pos χ ψ weight hcoeff ha0)
    htop (normFiberExpSum_flat_at_zero χ ψ weight hcoeff ha0)
end OAI.ShortDraftHeckeBridge
