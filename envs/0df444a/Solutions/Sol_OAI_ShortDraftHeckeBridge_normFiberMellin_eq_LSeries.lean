-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.normFiberMellin_eq_LSeries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:52:32.807682+00:00
-- url     : https://prove2.me/submissions/1938506f-8b76-4eea-a443-5ab8db948151

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberExpSum_mellin

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
    normFiberMellin weight s = LSeries (normFiberCoeff weight) s := by
  rw [normFiberMellin, normFiberExpSum_mellin χ ψ weight hcoeff ha0 hexp s hs]
  exact mul_div_cancel_left₀ _
    (Complex.Gamma_ne_zero_of_re_pos (lt_trans zero_lt_one hs))
end OAI.ShortDraftHeckeBridge
