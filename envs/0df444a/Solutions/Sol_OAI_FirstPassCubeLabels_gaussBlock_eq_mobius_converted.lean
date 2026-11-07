-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.gaussBlock_eq_mobius_converted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:45:04.639994+00:00
-- url     : https://prove2.me/submissions/f6572c2b-1014-4d33-ae03-00c28907b678

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_UniformKernelBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_FiniteOperator
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization
import Theorems.Thm_OAI_ActualEisensteinCubic_prime_product_moebius
import Theorems.Thm_OAI_MixedGaussConversion_neg_localGauss_eq_converted


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
open scoped BigOperators Classical
open OAI.FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (crossSymbol quadraticCrossPhase columnPrimeCoprime)
open FiniteGaussPhase (canonicalProductGauss)
namespace OAI.FirstPassCubeLabels
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) (side : Bool) :
    gaussBlock p hp hg S (fun _ => if side then 5 else 1) =
      FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) S *
        MixedCrossSeparation.convertedColumnBlock p hp hg S side := by
  have hinj : Function.Injective (fun i => Ideal.span {p i}) := by
    intro i k hik
    by_contra hne
    have ht := (hcop hne).sup_eq
    rw [hik, sup_idem] at ht
    exact (inferInstance : (Ideal.span {p k}).IsMaximal).ne_top ht
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  rw [FirstCauchyArithmetic.supportMobius,
    prime_product_moebius (fun i => Ideal.span {p i}) hprime hinj S]
  unfold gaussBlock MixedCrossSeparation.convertedColumnBlock
  rw [← Finset.prod_neg]
  apply Finset.prod_congr rfl
  intro i hi
  have hl := MixedGaussConversion.neg_localGauss_eq_converted (p i) (hp i) (hg i) (hc i) (hpr i) side
  change (∏ k ∈ S.erase i, crossSymbol p hg i k ^ (if side then 5 else 1)) *
      MixedGaussConversion.localGauss (p i) (hp i) (hg i) (if side then 5 else 1) =
    -((∏ k ∈ S.erase i, crossSymbol p hg i k ^ (if side then 5 else 1)) *
      MixedGaussConversion.convertedLocal (p i) (hp i) (hg i) side)
  rw [← hl]
  ring
end OAI.FirstPassCubeLabels
