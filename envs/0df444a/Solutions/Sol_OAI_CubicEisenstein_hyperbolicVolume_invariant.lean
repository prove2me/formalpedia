-- Prove2me | solution 1 for OAI.CubicEisenstein.hyperbolicVolume_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T05:22:46.112716+00:00
-- url     : https://prove2.me/submissions/e828fe1f-81d0-419f-99fd-94e87b757ab5

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ArithmeticBins
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_HyperbolicVolume
import Theorems.Thm_OAI_CubicEisenstein_complex_bruhat_nonzero
import Theorems.Thm_OAI_CubicEisenstein_complex_bruhat_zero
import Theorems.Thm_OAI_CubicEisenstein_complexTranslation_preserves_hyperbolicVolume
import Theorems.Thm_OAI_CubicEisenstein_complexDiagonal_preserves_hyperbolicVolume
import Theorems.Thm_OAI_CubicEisenstein_complexWeyl_preserves_hyperbolicVolume
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicVolume_invariant_mul

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
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix
namespace OAI.CubicEisenstein
theorem _root_.solution (g : SL(2,ℂ)) :
    Measure.map (fun w => g • w) hyperbolicVolume=hyperbolicVolume := by
  by_cases hc : g 1 0=0
  · obtain ⟨ha,hg⟩ := complex_bruhat_zero g hc
    rw [hg]
    exact hyperbolicVolume_invariant_mul _ _ (complexDiagonal_preserves_hyperbolicVolume _ ha)
      (complexTranslation_preserves_hyperbolicVolume _)
  · rw [complex_bruhat_nonzero g hc]
    exact hyperbolicVolume_invariant_mul _ _
      (hyperbolicVolume_invariant_mul _ _
        (hyperbolicVolume_invariant_mul _ _ (complexTranslation_preserves_hyperbolicVolume _)
          (complexDiagonal_preserves_hyperbolicVolume _ (inv_ne_zero hc)))
        complexWeyl_preserves_hyperbolicVolume)
      (complexTranslation_preserves_hyperbolicVolume _)
end OAI.CubicEisenstein
