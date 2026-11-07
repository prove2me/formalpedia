-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.activeRow_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:45:27.518921+00:00
-- url     : https://prove2.me/submissions/6095d773-d6da-4df5-a00c-e191ce1dd870

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_RadialFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ActiveConductor
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSexticRow_activeSupport
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_norm_le_one


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
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.ActualEisensteinCubic
open ConcreteTraceCRT EisensteinSchwartzPoisson
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S T : Finset ι) (h : O) :
    ‖finiteSexticRow (activePrimes P S T) (fun i => hgood i.val)
      (activeExponent S T) h‖ ≤ 1 := by
  rw [finiteSexticRow_activeSupport, norm_mul, norm_star]
  calc
    _ ≤ 1 * 1 := mul_le_mul
      (finiteSquarefreeRow_norm_le_one P hgood (S \ T) h)
      (finiteSquarefreeRow_norm_le_one P hgood (T \ S) h) (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul _
end OAI.ActualEisensteinCubic
