-- Prove2me | solution 1 for OAI.CompletedGauss.positive_log_scale_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:54:09.46453+00:00
-- url     : https://prove2.me/submissions/b848291e-d16a-4b77-8d37-290cdd33d083

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_PoissonSource
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_QuantitativePassage
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DyadicKernel

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
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open OAI.CompletedGauss
open ActualEisensteinCubic
namespace OAI.CompletedGauss
theorem _root_.solution (k n b K U B R : ℝ)
    (hk : 0<k) (hn : 0<n) (hb : 0<b) (hK : 0<K) (hU : 0<U) (hB : 0<B) :
    R*Real.exp (-2*Real.log (k/K)+Real.log (n/U)+3*Real.log (b/B))=
      R*(K/k)^2*(n/U)*(b/B)^3 := by
  have h2 : Real.exp ((2:ℝ)*Real.log (k/K))=(k/K)^2 := by
    rw [show (2:ℝ)=(2:ℕ) by rfl,Real.exp_nat_mul,Real.exp_log (div_pos hk hK)]
  have h3 : Real.exp ((3:ℝ)*Real.log (b/B))=(b/B)^3 := by
    rw [show (3:ℝ)=(3:ℕ) by rfl,Real.exp_nat_mul,Real.exp_log (div_pos hb hB)]
  rw [show -2*Real.log (k/K)+Real.log (n/U)+3*Real.log (b/B)=
      -(2*Real.log (k/K))+Real.log (n/U)+3*Real.log (b/B) by ring,
    Real.exp_add,Real.exp_add,Real.exp_neg,h2,h3,Real.exp_log (div_pos hn hU)]
  field_simp
end OAI.CompletedGauss
