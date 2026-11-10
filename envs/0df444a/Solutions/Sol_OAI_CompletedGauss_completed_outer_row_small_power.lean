-- Prove2me | solution 1 for OAI.CompletedGauss.completed_outer_row_small_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:25:45.531748+00:00
-- url     : https://prove2.me/submissions/f4de1b26-c520-4ed1-81ad-3b97d768392c

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_InputEnergy
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_QuantitativePassage
import Theorems.Thm_OAI_CompletedGauss_completed_outer_row_sum_bound
import Theorems.Thm_OAI_IdealDivisorBound_ideal_divisor_small_power


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
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open OAI.CompletedGauss
open ActualEisensteinCubic CanonicalQuadraticSieve IdealMobiusDivisorSum
namespace OAI.CompletedGauss
theorem _root_.solution (ε : ℝ) (hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀(S : Finset (Ideal O)) (Q : Ideal O),Q≠0 →
      ∀(f : Ideal O→ℝ) (C : ℝ),0≤C →
      (∀A∈S.image rowPowerfulPart,∀T∈S.image (fun I => rowMaskPart I Q),
        (∑I∈completedRowFiber S Q A T,f I)≤C/(Ideal.absNorm A:ℝ)) →
      (∑I∈S,f I)≤D*(Ideal.absNorm Q:ℝ)^ε*C := by
  obtain ⟨D,hD,hbound⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨1048576*D,by positivity,?_⟩
  intro S Q hQ f C hC hblocks
  apply (completed_outer_row_sum_bound S Q hQ f C hC hblocks).trans
  have hh := mul_le_mul_of_nonneg_right (hbound Q hQ) hC
  nlinarith
end OAI.CompletedGauss
