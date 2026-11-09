-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.originalHigh_gcd_eq_maskedPoissonDifference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T04:27:43.008599+00:00
-- url     : https://prove2.me/submissions/a6d9a038-492e-4fee-ad26-34161269fc1f

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonComparison
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ArithmeticBins
import Theorems.Thm_OAI_CanonicalQuadraticSieve_admissible_idealQuotient
import Theorems.Thm_OAI_CanonicalQuadraticSieve_columnRay_idealQuotient_eq
import Theorems.Thm_OAI_CanonicalQuadraticSieve_commonMaskIdeal_squarefree
import Theorems.Thm_OAI_CanonicalQuadraticSieve_maskedDualFamily_retained
import Theorems.Thm_OAI_CanonicalQuadraticSieve_originalHigh_gcd_principal_assembly


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
open scoped BigOperators Classical SchwartzMap
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n]
    (D : Ideal O) (hD : D≠0) (cols : n → Ideal O) (hcols : ∀j, Admissible (cols j))
    (hdiv : ∀j, D∣cols j) (hproper : ∀j, cols j≠D)
    (hray : ∀j k, columnRay (cols j)=columnRay (cols k))
    (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) :
    (∑j, ∑k, if gcd (cols j) (cols k)=D then
      star (a j)*a k*(∑' lengthScale : Ideal O, originalPairHigh (cols j) (cols k) W M K lengthScale) else 0) =
    maskedPoissonDifference (commonMaskIdeal D) W (fun j => idealQuotient D (cols j)) a M K := by
  rw [originalHigh_gcd_principal_assembly D hD cols hcols hdiv hproper hray a W M K hM,
    maskedPoissonDifference,
    maskedDualFamily_retained _ (commonMaskIdeal_squarefree D).ne_zero _ a W M K hM
      (fun j => admissible_idealQuotient (hcols j) (hdiv j))
      (fun j k => columnRay_idealQuotient_eq D (cols j) (cols k) (hcols j) (hcols k)
        (hdiv j) (hdiv k) (hray j k))]
end OAI.CanonicalQuadraticSieve
