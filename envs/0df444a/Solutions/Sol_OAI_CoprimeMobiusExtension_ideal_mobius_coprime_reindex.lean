-- Prove2me | solution 1 for OAI.CoprimeMobiusExtension.ideal_mobius_coprime_reindex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:31:20.9324+00:00
-- url     : https://prove2.me/submissions/9a157747-830a-4613-ab5a-362f4fb468db

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SquarePhaseFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_MixedConversion
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CrossSeparation
import Theorems.Thm_OAI_CoprimeMobiusExtension_double_sum_disjoint_reindexed
import Theorems.Thm_OAI_ActualEisensteinCubic_prime_product_moebius


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
open OAI.CoprimeMobiusExtension
open ActualEisensteinCubic
namespace OAI.CoprimeMobiusExtension
theorem _root_.solution
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (B : Finset ι) (Z : Ideal O → Ideal O → ℂ) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
      if Disjoint S T then Z (∏ i ∈ S, P i) (∏ i ∈ T, P i) else 0) =
      ∑ D ∈ B.powerset, (UniqueFactorizationMonoid.moebius (∏ i ∈ D, P i) : ℂ) *
        ∑ U ∈ (B \ D).powerset, ∑ V ∈ (B \ D).powerset,
          Z ((∏ i ∈ D, P i) * ∏ i ∈ U, P i) ((∏ i ∈ D, P i) * ∏ i ∈ V, P i) := by
  rw [double_sum_disjoint_reindexed]
  apply Finset.sum_congr rfl
  intro D hD
  rw [prime_product_moebius P hprime hinj]
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  rw [Finset.prod_union (Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right)]
  rw [Finset.prod_union (Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hV) disjoint_sdiff_self_right)]
end OAI.CoprimeMobiusExtension
