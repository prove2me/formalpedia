-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.normFiberExpSum_mellin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:50:57.843726+00:00
-- url     : https://prove2.me/submissions/f4a42a72-d11f-44e6-8e1f-e06911f80ebf

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Theorems.Thm_OAI_ShortDraftHeckeBridge_pairInverseCoeff_LSeriesSummable
import Theorems.Thm_OAI_ShortDraftMellin_mellin_of_exponential_smoothing


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
    (hexp : ∀ t : ℝ, 0 < t → Summable
      (fun n : ℕ => normFiberCoeff weight n * Real.exp (-(n : ℝ) * t)))
    (s : ℂ) (hs : 1 < s.re) :
    mellin (fun D : ℝ => normFiberExpSum weight D⁻¹) (-s) =
      Complex.Gamma s * LSeries (normFiberCoeff weight) s := by
  apply ShortDraftMellin.mellin_of_exponential_smoothing
    (normFiberCoeff weight) (normFiberExpSum weight) s hs ha0
  · intro t ht
    exact (hexp t ht).hasSum
  · exact (LSeriesSummable_congr s (fun {n} hn => hcoeff n hn)).mpr
      (pairInverseCoeff_LSeriesSummable χ ψ s hs)
end OAI.ShortDraftHeckeBridge
