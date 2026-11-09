-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.poisson_truncation_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T05:03:38.398202+00:00
-- url     : https://prove2.me/submissions/9b0329c7-cc0c-4e5c-b16f-0a3eabb9e545

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GlobalBinLoss
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonConstants
import Theorems.Thm_OAI_CanonicalQuadraticSieve_power_cutoff_dominates

set_option autoImplicit false
open OAI
noncomputable section
open OAI.CanonicalQuadraticSieve
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
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (P T η K M N C1 : ℝ) (l : ℕ)
    (hP : 1≤P) (hT : P^η≤T) (hpow : 4≤η*l)
    (_hK : 0≤K) (hM : 0≤M) (hN : 0≤N) (hC1 : 0≤C1)
    (hKP : K≤C1*P^3) (hMP : M≤P) (hNP : N≤P) :
    K*M/T^l≤C1 ∧ K*N/T^l≤C1 := by
  have hp0 : 0<P := by linarith
  have htpos : 0<T := lt_of_lt_of_le (Real.rpow_pos_of_pos hp0 _) hT
  have hcut := power_cutoff_dominates P T η l hP hT hpow
  have hb (Y : ℝ) (hY : 0≤Y) (hYP : Y≤P) : K*Y/T^l≤C1 := by
    apply (div_le_iff₀ (pow_pos htpos _)).mpr
    calc
      K*Y ≤ (C1*P^3)*P := by gcongr
      _ = C1*P^4 := by ring
      _ ≤ C1*T^l := by gcongr
  exact ⟨hb M hM hMP,hb N hN hNP⟩
end OAI.CanonicalQuadraticSieve
