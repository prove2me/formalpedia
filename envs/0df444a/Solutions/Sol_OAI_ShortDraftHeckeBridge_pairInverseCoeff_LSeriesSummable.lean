-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.pairInverseCoeff_LSeriesSummable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:49:31.911522+00:00
-- url     : https://prove2.me/submissions/4a4bf379-9592-4c15-8894-2dda7ab71412

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin

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
    (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (pairInverseCoeff χ ψ) s := by
  have hχ : LSeriesSummable
      (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) s :=
    DirichletCharacter.LSeriesSummable_mul χ
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  have hψ : LSeriesSummable
      (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ)) s :=
    DirichletCharacter.LSeriesSummable_mul ψ
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  exact hχ.convolution hψ
end OAI.ShortDraftHeckeBridge
