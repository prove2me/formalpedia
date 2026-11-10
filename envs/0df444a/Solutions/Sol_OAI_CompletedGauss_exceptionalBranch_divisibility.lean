-- Prove2me | solution 1 for OAI.CompletedGauss.exceptionalBranch_divisibility
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:01:53.694567+00:00
-- url     : https://prove2.me/submissions/92ece84b-ebf7-4743-a4bd-bb8eb58de4a6

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_PowerfulParts
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_LogarithmicBins
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RowCaps
import Theorems.Thm_OAI_CompletedGauss_exceptionalBranch_support

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
open scoped BigOperators Classical
open OAI.CompletedGauss
open ActualEisensteinCubic LocalReflectionBrackets
namespace OAI.CompletedGauss
theorem _root_.solution {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (e : ι→Fin 3) (n b : O) (hne : exceptionalBranch P e n b≠0) :
    exceptionalDivisor P e 1 ∣ Ideal.span {n} ∧
    exceptionalDivisor P e 2 ∣ Ideal.span {b} ∧
    (∀i,e i=2 → n∉P i) := by
  have hs := exceptionalBranch_support P e n b hne
  have hprod (v : Fin 3) (z : O) (hz : ∀i,e i=v → z∈P i) :
      exceptionalDivisor P e v ∣ Ideal.span {z} := by
    rw [exceptionalDivisor]
    apply Fintype.prod_dvd_of_coprime
    · intro i j hij
      change IsCoprime (if e i=v then P i else 1) (if e j=v then P j else 1)
      by_cases hi : e i=v
      · rw [if_pos hi]
        by_cases hj : e j=v
        · rw [if_pos hj]
          exact hcop hij
        · rw [if_neg hj]
          exact isCoprime_one_right
      · rw [if_neg hi]
        exact isCoprime_one_left
    · intro i
      split_ifs with hi
      · rw [Ideal.dvd_iff_le,Ideal.span_le,Set.singleton_subset_iff,SetLike.mem_coe]
        exact hz i hi
      · exact one_dvd _
  exact ⟨hprod 1 n hs.1,hprod 2 b (fun i hi => (hs.2 i hi).2),fun i hi => (hs.2 i hi).1⟩
end OAI.CompletedGauss
