-- Prove2me | solution 1 for OAI.CompletedGauss.squarefreeMaskPart_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T08:56:54.486939+00:00
-- url     : https://prove2.me/submissions/8fcab46b-cf71-4965-b597-5a69fcf571c4

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_SquarefreeTransfer
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeBlocks
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_PowerfulParts
import Theorems.Thm_OAI_CompletedGauss_squarefreeMaskPart_ne_zero
import Theorems.Thm_OAI_CompletedGauss_normalizedFactors_squarefreeMaskPart

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
open OAI.CompletedGauss
open ActualEisensteinCubic CanonicalQuadraticSieve UniqueFactorizationMonoid
namespace OAI.CompletedGauss
theorem _root_.solution (I R : Ideal O) (hI : Squarefree I) : squarefreeMaskPart I R∣R := by
  by_cases hR : R=0
  · rw [hR]; exact dvd_zero _
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (squarefreeMaskPart_ne_zero I R) hR).mpr
  rw [normalizedFactors_squarefreeMaskPart]
  apply Multiset.le_iff_count.mpr
  intro P
  rw [Multiset.count_filter]
  split_ifs with hp
  · have hn := Multiset.nodup_iff_count_le_one.mp ((squarefree_iff_nodup_normalizedFactors hI.ne_zero).mp hI) P
    by_cases hz : (normalizedFactors I).count P=0
    · omega
    · have hm := Multiset.count_pos.mp (Nat.pos_of_ne_zero hz)
      have hr := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hR).mpr ⟨prime_of_normalized_factor P hm,hp⟩
      have hc := Multiset.count_pos.mpr hr
      omega
  · omega
end OAI.CompletedGauss
