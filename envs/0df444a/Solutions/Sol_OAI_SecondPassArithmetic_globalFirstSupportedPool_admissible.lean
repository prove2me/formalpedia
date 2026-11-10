-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalFirstSupportedPool_admissible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T07:26:17.041719+00:00
-- url     : https://prove2.me/submissions/f2250db2-bb87-4814-ab3c-b7df17115ba3

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LiteralSources
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PooledRows
import Theorems.Thm_OAI_SecondPassArithmetic_mem_globalFirstExpansionPool
import Theorems.Thm_OAI_SecondPassArithmetic_mem_secondExpansionPool


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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
variable (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
omit [∀ (i : ι), (span {p i}).IsMaximal]
namespace OAI.SecondPassArithmetic
theorem _root_.solution (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (hs : ∀ b∈s,GlobalFirstAdmissible b)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (ell M : ℝ) (side : Bool) (x : GlobalSecondData ι)
    (hx : x∈globalFirstSupportedPool p pool s cutoff ell M side) : GlobalSecondAdmissible x := by
  have hm := (mem_globalFirstExpansionPool pool s cutoff x).mp (Finset.mem_filter.mp hx).1
  have hb := hs x.first hm.1
  have hE := ((mem_secondExpansionPool _ _ x.source).mp hm.2).2.1
  exact ⟨hb.1,hE,hb.2.1,hb.2.2⟩
end OAI.SecondPassArithmetic
