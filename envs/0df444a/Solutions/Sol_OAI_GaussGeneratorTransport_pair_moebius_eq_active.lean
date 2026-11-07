-- Prove2me | solution 1 for OAI.GaussGeneratorTransport.pair_moebius_eq_active
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:11:00.385966+00:00
-- url     : https://prove2.me/submissions/962410d8-870b-4ff1-8e77-a3942ddee373

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ActiveConductor
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_MixedConversion
import Theorems.Thm_OAI_ActualEisensteinCubic_prime_product_moebius
import Theorems.Thm_OAI_FiniteGaussPhase_product_moebius_eq_sign


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
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.GaussGeneratorTransport
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase
open MixedGaussConversion
namespace OAI.GaussGeneratorTransport
theorem _root_.solution
    {ι : Type*} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (S T : Finset ι) :
    (UniqueFactorizationMonoid.moebius (∏ i ∈ S, Ideal.span {p i}) : ℂ) *
      (UniqueFactorizationMonoid.moebius (∏ i ∈ T, Ideal.span {p i}) : ℂ) =
      (UniqueFactorizationMonoid.moebius
        (Ideal.span {∏ i : activeSupport S T, p i.val}) : ℂ) := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hcop := activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T
  rw [prime_product_moebius (fun i => Ideal.span {p i}) hprime hinj S,
    prime_product_moebius (fun i => Ideal.span {p i}) hprime hinj T,
    product_moebius_eq_sign (fun i : activeSupport S T => p i.val) hcop, ← pow_add]
  have hd : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have ha : Fintype.card (activeSupport S T) = (S \ T).card + (T \ S).card := by
    rw [Fintype.card_coe, activeSupport, Finset.card_union_of_disjoint hd]
  have hs := Finset.card_sdiff_add_card_inter S T
  have ht := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm T S] at ht
  have hcard : S.card + T.card = Fintype.card (activeSupport S T) + 2 * (S ∩ T).card := by omega
  rw [hcard, pow_add, pow_mul]
  norm_num
end OAI.GaussGeneratorTransport
