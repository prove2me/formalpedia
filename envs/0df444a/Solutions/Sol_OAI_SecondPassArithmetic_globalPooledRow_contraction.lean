-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalPooledRow_contraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T04:32:17.45945+00:00
-- url     : https://prove2.me/submissions/bc94620a-1a79-4a32-ab5f-4c20c39f9f49

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonComparison
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ArithmeticBins
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledDelta_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledNaturalRow_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledNaturalRow_bound
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooled_radial_ratio


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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.SecondPassArithmetic
theorem _root_.solution (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) (hJ : globalLogRep j 4 ≤ B^2)
    (hretained : globalBinRadial ell (globalPooledRowScale K ell B F j) j ≤ globalPooledDelta B F j) :
    globalLogRep j 8*Real.exp 1 ≤ K/globalPooledDelta B F j := by
  have hD := globalPooledDelta_pos B F hB hF j
  have hN := globalPooledNaturalRow_pos K B F hK hB hF j
  have hn := globalPooledNaturalRow_bound K B F hK hB hF j hJ
  have hr := hretained
  rw [globalBinRadial,globalPooled_radial_ratio K ell B F hK hell hB hF] at hr
  have hr' : globalLogRep j 8*Real.exp 1 ≤ globalPooledDelta B F j*globalPooledNaturalRow K B F j := by
    apply (div_le_iff₀ hN).mp
    convert hr using 1 <;> first | rfl | ring
  calc
    _ ≤ globalPooledDelta B F j*globalPooledNaturalRow K B F j := hr'
    _ ≤ globalPooledDelta B F j*(K/(globalPooledDelta B F j)^2) := by gcongr
    _ = _ := by field_simp
end OAI.SecondPassArithmetic
