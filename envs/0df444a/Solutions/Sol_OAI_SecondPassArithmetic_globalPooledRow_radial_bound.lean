-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalPooledRow_radial_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T05:50:22.796312+00:00
-- url     : https://prove2.me/submissions/3ba95f35-e48c-465f-a2e1-2d92704fd70e

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FundamentalDomain
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GlobalScales
import Theorems.Thm_OAI_SecondPassArithmetic_globalBinRadial_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledDelta_ge
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledDelta_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledNaturalRow_bound
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledNaturalRow_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledRowScale_pos
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
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic
open SecondPassIntegration (densityChildEnergy)
namespace OAI.SecondPassArithmetic
theorem _root_.solution (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 1 ≤ B) (hF : 1 ≤ F) (j : GlobalLogIndex) (hJ : globalLogRep j 4 ≤ B^2) :
    globalLogRep j 8*Real.exp 1 ≤ globalBinRadial ell (globalPooledRowScale K ell B F j) j*K := by
  have hB0 := zero_lt_one.trans_le hB
  have hF0 := zero_lt_one.trans_le hF
  have hD := globalPooledDelta_pos B F hB0 hF0 j
  have hD1 : 1 ≤ globalPooledDelta B F j :=
    (one_le_mul_of_one_le_of_one_le hB hF).trans (globalPooledDelta_ge B F hB0.le hF0.le j)
  have hN := globalPooledNaturalRow_pos K B F hK hB0 hF0 j
  have hR := globalBinRadial_pos ell (globalPooledRowScale K ell B F j) hell
    (globalPooledRowScale_pos K ell B F hK hell hB0 hF0 j) j
  have he : globalLogRep j 8*Real.exp 1 =
      globalBinRadial ell (globalPooledRowScale K ell B F j) j*globalPooledNaturalRow K B F j := by
    rw [globalBinRadial,globalPooled_radial_ratio K ell B F hK hell hB0 hF0]
    field_simp
  calc
    _ = _ := he
    _ ≤ globalBinRadial ell (globalPooledRowScale K ell B F j) j*(K/(globalPooledDelta B F j)^2) :=
      mul_le_mul_of_nonneg_left (globalPooledNaturalRow_bound K B F hK hB0 hF0 j hJ) hR.le
    _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_self hK.le (one_le_pow₀ hD1)) hR.le
end OAI.SecondPassArithmetic
