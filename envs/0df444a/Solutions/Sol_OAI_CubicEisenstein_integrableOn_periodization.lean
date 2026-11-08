-- Prove2me | solution 1 for OAI.CubicEisenstein.integrableOn_periodization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:30:44.907469+00:00
-- url     : https://prove2.me/submissions/e8a82a65-5ddb-4276-8dfd-1641dce10b18

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_HyperbolicSpace
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RowMajorants
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FourierCoefficients
import Theorems.Thm_OAI_CubicEisenstein_periodization_lintegral_norm_ne_top


set_option autoImplicit false
open OAI
noncomputable section
open OAI.CubicEisenstein
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
open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal
open ActualEisensteinCubic ConcreteTraceCRT
namespace OAI.CubicEisenstein
theorem _root_.solution (f : ℂ → ℂ) (hf : Integrable f) :
    IntegrableOn (fun z => ∑' n : O,f (z+3*eisEmbedding n)) periodDomain := by
  let : Countable O := latticeCoordEquiv.injective.countable
  have hm (n : O) : AEStronglyMeasurable (fun z => f (z+3*eisEmbedding n))
      (volume.restrict periodDomain) :=
    (hf.comp_add_right (3*eisEmbedding n)).aestronglyMeasurable.restrict
  refine ⟨AEStronglyMeasurable.tsum hm, ?_⟩
  change (∫⁻ z in periodDomain,‖∑' n : O,f (z+3*eisEmbedding n)‖ₑ)<⊤
  apply lt_of_le_of_lt (lintegral_mono fun z => enorm_tsum_le_tsum_enorm) _
  rw [lintegral_tsum (fun n => (hm n).enorm)]
  exact lt_top_iff_ne_top.mpr (periodization_lintegral_norm_ne_top f hf)
end OAI.CubicEisenstein
