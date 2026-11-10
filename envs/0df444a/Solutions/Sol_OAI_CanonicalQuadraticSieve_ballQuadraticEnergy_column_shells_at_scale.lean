-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.ballQuadraticEnergy_column_shells_at_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:13:58.718129+00:00
-- url     : https://prove2.me/submissions/f2bfeb7f-488c-4556-aad7-ca90b63c568a

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GlobalScales
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularLifting
import Theorems.Thm_OAI_CanonicalQuadraticSieve_ballQuadraticEnergy_coefficientAtScale
import Theorems.Thm_OAI_CanonicalQuadraticSieve_ballQuadraticEnergy_column_shells
import Theorems.Thm_OAI_CanonicalQuadraticSieve_dyadicColumnCoefficient_shell


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
open ActualEisensteinCubic CompletedGauss
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (M N : ℝ) (lengthScale : ℕ) (hNL : N≤(2:ℝ)^lengthScale)
    (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ (lengthScale+1:ℝ)*∑j : Fin (lengthScale+1),
      ballQuadraticEnergy M ((2:ℝ)^j.val)
        (coefficientAtScale N ((2:ℝ)^j.val) (dyadicColumnCoefficient N lengthScale hNL j a)) := by
  apply (ballQuadraticEnergy_column_shells M N lengthScale hNL a).trans_eq
  apply congrArg (fun x : ℝ => (lengthScale + 1 : ℝ) * x)
  apply Finset.sum_congr rfl
  intro j _
  exact ballQuadraticEnergy_coefficientAtScale M N _ _
    (fun J hJ => (dyadicColumnCoefficient_shell N lengthScale hNL j a J hJ).2)
end OAI.CanonicalQuadraticSieve
