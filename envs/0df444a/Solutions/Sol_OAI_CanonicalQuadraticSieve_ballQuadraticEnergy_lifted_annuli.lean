-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.ballQuadraticEnergy_lifted_annuli
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:20:59.956514+00:00
-- url     : https://prove2.me/submissions/ff4e6158-72d9-446c-91b9-4a463cad7a48

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GlobalScales
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularLifting
import Theorems.Thm_OAI_CanonicalQuadraticSieve_squarefreeHigh_energy_le_annuli
import Theorems.Thm_OAI_CanonicalQuadraticSieve_liftingFreeCoefficient_coprime
import Theorems.Thm_OAI_CanonicalQuadraticSieve_liftingDividedCoefficient_coprime
import Theorems.Thm_OAI_CanonicalQuadraticSieve_liftingCoefficient_row_energy
import Theorems.Thm_OAI_CanonicalQuadraticSieve_ballQuadraticEnergy_low_high

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
open scoped BigOperators Classical
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss FiniteSieveOperator
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (M N K : ℝ) (hM : 0<M) (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ sieveNorm K N*(∑J, ‖a J‖^2) +
      2*((∑j : Fin 7, annularHighEnergy ((2:ℝ)^j.val*M) N K (liftingFreeCoefficient N a)) +
        ∑j : Fin 7, annularHighEnergy ((2:ℝ)^j.val*M) N K (liftingDividedCoefficient N a)) := by
  have hlo := ballQuadraticEnergy_low_high M N K a
  have hs : (∑I : squarefreeHighRange M K,
      ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J‖^2) ≤
      2*((∑I : squarefreeHighRange M K,
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingFreeCoefficient N a J‖^2) +
        ∑I : squarefreeHighRange M K,
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingDividedCoefficient N a J‖^2) := by
    calc
      _ ≤ ∑I : squarefreeHighRange M K, 2*(
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingFreeCoefficient N a J‖^2 +
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingDividedCoefficient N a J‖^2) :=
        Finset.sum_le_sum (fun I _ => liftingCoefficient_row_energy N a (primaryGenerator I.val))
      _ = _ := by rw [←Finset.mul_sum,Finset.sum_add_distrib]
  have hfree := squarefreeHigh_energy_le_annuli M N K hM (liftingFreeCoefficient N a)
    (liftingFreeCoefficient_coprime N a)
  have hdiv := squarefreeHigh_energy_le_annuli M N K hM (liftingDividedCoefficient N a)
    (liftingDividedCoefficient_coprime N a)
  linarith
end OAI.CanonicalQuadraticSieve
