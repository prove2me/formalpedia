-- Prove2me | solution 1 for OAI.SecondPassArithmetic.canonicalCubeBeforePoisson_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T23:44:46.6523+00:00
-- url     : https://prove2.me/submissions/e0e3241d-6531-48fe-b0f4-4b90e17d3869

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DualZeroMode
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_CanonicalDensity
import Theorems.Thm_OAI_ActualEisensteinCubic_primeSubsetGenerator_ne_zero
import Theorems.Thm_OAI_FirstPassCubeLabels_actualFirstKernel_truncate
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalCubeBeforePoisson_eq_all_modes


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
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels
variable {ι:Type*} [DecidableEq ι]
  (p:ι→OAI.SecondPassArithmetic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) (T:Finset ι→Finset O)
    (hT:∀D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,(0:O)∈T D):
    canonicalCubeBeforePoisson p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K=
      canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K+
      canonicalCubeDualFinite p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K T+
      canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K T := by
  rw [canonicalCubeBeforePoisson_eq_all_modes p hp hcop hg hinj hc]
  · unfold canonicalCubeDualZero canonicalCubeDualFinite canonicalCubeDualTail
    rw [←mul_add,←mul_add,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply congrArg
    apply Finset.sum_congr rfl
    intro D hD
    rw [actualFirstKernel_truncate p hp hcop hg _ _ _ _ _ _ _ _ _ _ _ _ _ hK _
      (primeSubsetGenerator_ne_zero _ _) (T D)]
    rw [←Finset.sum_erase_add _ _ (hT D hD)]
    ring
  · exact hK
end OAI.SecondPassArithmetic
