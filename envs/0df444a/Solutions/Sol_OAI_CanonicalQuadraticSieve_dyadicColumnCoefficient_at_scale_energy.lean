-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.dyadicColumnCoefficient_at_scale_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:02:27.84585+00:00
-- url     : https://prove2.me/submissions/2373934d-2b2b-4635-baaf-29a84b3f359c

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_FrequencyCutoffs
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ConstantDirichletSeries
import Theorems.Thm_OAI_CanonicalQuadraticSieve_dyadicColumnCoefficient_shell
import Theorems.Thm_OAI_CanonicalQuadraticSieve_dyadicColumnCoefficient_energy
import Theorems.Thm_OAI_CanonicalQuadraticSieve_coefficientAtScale_energy

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
open scoped BigOperators Classical
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss FiniteSieveRestriction
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (a : idealRange N → ℂ) :
    (∑ j : Fin (lengthScale + 1), ∑ J : idealRange ((2 : ℝ) ^ j.val),
      ‖coefficientAtScale N ((2 : ℝ) ^ j.val) (dyadicColumnCoefficient N lengthScale hNL j a) J‖ ^ 2) =
        ∑ J : idealRange N, ‖a J‖ ^ 2 := by
  calc
    _ = ∑ j : Fin (lengthScale + 1), ∑ J : idealRange N, ‖dyadicColumnCoefficient N lengthScale hNL j a J‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact (coefficientAtScale_energy N _ _
        (fun J hJ => (dyadicColumnCoefficient_shell N lengthScale hNL j a J hJ).2)).symm
    _ = _ := dyadicColumnCoefficient_energy N lengthScale hNL a
end OAI.CanonicalQuadraticSieve
