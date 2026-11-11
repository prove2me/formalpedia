-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalPooled_mass_le_parent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:08:19.477368+00:00
-- url     : https://prove2.me/submissions/9ec4f8c7-d599-450f-931a-bf31459779c4

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_RetainedDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_CanonicalTailBounds
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledDelta_ge
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledDelta_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooled_mass


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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.SecondPassArithmetic
theorem _root_.solution (_K ell B F:ℝ) (hell:0<ell) (hB:0<B) (hF:0<F)
    (j:GlobalLogIndex) (hJ:globalLogRep j 4≤B^2) (hlarge:Real.exp 4≤B*F):
    globalPooledColumnScale ell j*globalPooledLabelScale j≤(ell*B^3)*F := by
  have hD:=globalPooledDelta_pos B F hB hF j
  have hM:0<(ell*B^3)*F:=by positivity
  rw [globalPooled_mass ell B F hB hF j]
  calc
    _ ≤ Real.exp 4*((ell*B^3)*F)*B^2/(globalPooledDelta B F j*B^2):=by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = Real.exp 4*((ell*B^3)*F)/globalPooledDelta B F j:=by field_simp
    _ ≤ (ell*B^3)*F:=by
      apply (div_le_iff₀ hD).mpr
      have he:=hlarge.trans (globalPooledDelta_ge B F hB.le hF.le j)
      nlinarith
end OAI.SecondPassArithmetic
