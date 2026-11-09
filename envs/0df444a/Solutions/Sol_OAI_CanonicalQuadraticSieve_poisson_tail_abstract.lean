-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.poisson_tail_abstract
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T05:03:39.469075+00:00
-- url     : https://prove2.me/submissions/2123d3e1-a584-4b90-aafb-bd64059c8b74

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
theorem _root_.solution (B P t K η M : ℝ) (A : ℕ)
    (hB : 1≤B) (hP : 1≤P) (hM : 0≤M)
    (ht : 1/(B*P^2)≤t) (hu : P^η≤1+t*K) (hA : 4≤η*A) :
    M/((min 1 t)^2*(1+t*K)^A)≤B^2*M := by
  have hB0 : 0<B := by linarith
  have hP0 : 0<P := by linarith
  have hBP : 1≤B*P^2 := by nlinarith [sq_nonneg (P-1)]
  have hinv : 1/(B*P^2)≤1 := (div_le_one (by positivity)).mpr hBP
  have htlo : 1/(B*P^2)≤min 1 t := le_min hinv ht
  have htpos : 0<min 1 t := lt_of_lt_of_le (by positivity) htlo
  have hup : 0<1+t*K := lt_of_lt_of_le (Real.rpow_pos_of_pos hP0 _) hu
  have hpow := power_cutoff_dominates P (1+t*K) η A hP hu hA
  have hprod : 1/B^2≤(min 1 t)^2*(1+t*K)^A := by
    calc
      1/B^2 = (1/(B*P^2))^2*P^4 := by field_simp
      _ ≤ (min 1 t)^2*(1+t*K)^A := by gcongr
  apply (div_le_iff₀ (by positivity : 0<(min 1 t)^2*(1+t*K)^A)).mpr
  have hh := mul_le_mul_of_nonneg_left hprod (show 0≤B^2*M by positivity)
  have he : (B^2*M)*(1/B^2)=M := by field_simp
  rw [he] at hh
  exact hh
end OAI.CanonicalQuadraticSieve
