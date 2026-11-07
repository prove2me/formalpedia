-- Prove2me | solution 1 for OAI.MixedGaussConversion.canonicalSextic_fifth_eq_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:10:59.662978+00:00
-- url     : https://prove2.me/submissions/8441236c-d17a-48af-9e76-d7cb117c7247

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ActiveConductor
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_MixedConversion
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_conj_as_row_label


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
theorem _root_.solution (p : O) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) :
    canonicalSextic (Ideal.span {p}) hg ^ 5 = (canonicalSextic (Ideal.span {p}) hg)⁻¹ := by
  apply DFunLike.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [MulChar.pow_apply' _ (by decide : (5 : ℕ) ≠ 0), ← MulChar.star_apply',
    canonicalSextic_conj_as_row_label]
  ring
end OAI.MixedGaussConversion
