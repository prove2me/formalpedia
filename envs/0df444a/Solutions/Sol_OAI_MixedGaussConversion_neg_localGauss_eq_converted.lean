-- Prove2me | solution 1 for OAI.MixedGaussConversion.neg_localGauss_eq_converted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:18:07.04588+00:00
-- url     : https://prove2.me/submissions/00f51a1f-5d7a-4fd6-9738-eef1aff609ef

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ActiveConductor
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_MixedConversion
import Theorems.Thm_OAI_MixedGaussConversion_local_sign_conversion
import Theorems.Thm_OAI_MixedGaussConversion_norm_localG

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
open OAI.MixedGaussConversion
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase
namespace OAI.MixedGaussConversion
theorem _root_.solution (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : lambda ^ 2 ∣ p - 1) (inverse : Bool) :
    -localGauss p hp hg (if inverse then 5 else 1) = convertedLocal p hp hg inverse := by
  have hG : localG p hp hg ≠ 0 := by
    intro hz
    have hn := norm_localG p hp hg hchar hprimary
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  cases inverse
  · exact (eq_div_iff (star_ne_zero.mpr hG)).mpr
      (local_sign_conversion p hp hg hchar hprimary).1
  · exact (eq_div_iff hG).mpr (local_sign_conversion p hp hg hchar hprimary).2
end OAI.MixedGaussConversion
