-- Prove2me | solution 1 for OAI.CubicEisenstein.actual_spatial_continuousAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T15:32:29.008264+00:00
-- url     : https://prove2.me/submissions/16d255d3-9335-4788-8523-bf81630ad59c

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_GreenIdentity
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LogarithmicTargets
import Theorems.Thm_OAI_CubicEisenstein_rowSmoothPower_continuousAt
import Theorems.Thm_OAI_CubicEisenstein_smoothCoefficients_continuousAt
import Theorems.Thm_OAI_CubicEisenstein_spatial_summable_derivative_bounds
import Theorems.Thm_OAI_CubicEisenstein_eisensteinPartials_eq_tsum
import Theorems.Thm_OAI_CubicEisenstein_embeddedRow_ne_zero
import Theorems.Thm_OAI_CubicEisenstein_upperEisensteinField_eq_smooth


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
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open OAI.CubicEisenstein
namespace OAI.CubicEisenstein
theorem _root_.solution (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    ContinuousAt (upperEisensteinField s) p ∧ ∀j : Fin 3,
    ContinuousAt (eisensteinFirstPartial s j) p ∧
    ContinuousAt (eisensteinSecondPartial s j) p := by
  obtain ⟨U,hU,hpU,M₀,M₁,M₂,hM₀,hM₁,hM₂,hbound⟩ := spatial_summable_derivative_bounds s hs p hv
  have hf (r : CuspCosets) : ContinuousOn (smoothSummand s r) U := by
    intro q hq
    exact ((rowSmoothPower_continuousAt s (embeddedRow r) (embeddedRow_ne_zero r) q
      (hbound q hq).1).const_mul _).continuousWithinAt
  have hsum := continuousOn_tsum hf hM₀ (fun r q hq => ((hbound q hq).2 r).1)
  have heq : (upperEisensteinField s) =ᶠ[𝓝 p] smoothEisenstein s := by
    filter_upwards [hU.mem_nhds hpU] with q hq
    exact upperEisensteinField_eq_smooth s q (hbound q hq).1
  refine ⟨(hsum.continuousAt (hU.mem_nhds hpU)).congr heq.symm,fun j => ?_⟩
  have hc₁ (r : CuspCosets) : ContinuousOn (smoothFirstCoefficient s r j) U := by
    intro q hq
    exact ((smoothCoefficients_continuousAt s r j q (hbound q hq).1).1).continuousWithinAt
  have hc₂ (r : CuspCosets) : ContinuousOn (smoothSecondCoefficient s r j) U := by
    intro q hq
    exact ((smoothCoefficients_continuousAt s r j q (hbound q hq).1).2).continuousWithinAt
  have hsum₁ := continuousOn_tsum hc₁ hM₁ (fun r q hq => (((hbound q hq).2 r).2 j).1)
  have hsum₂ := continuousOn_tsum hc₂ hM₂ (fun r q hq => (((hbound q hq).2 r).2 j).2)
  have heq₁ : eisensteinFirstPartial s j =ᶠ[𝓝 p] (fun q => ∑'r,smoothFirstCoefficient s r j q) := by
    filter_upwards [hU.mem_nhds hpU] with q hq
    exact (eisensteinPartials_eq_tsum s hs j q (hbound q hq).1).1
  have heq₂ : eisensteinSecondPartial s j =ᶠ[𝓝 p] (fun q => ∑'r,smoothSecondCoefficient s r j q) := by
    filter_upwards [hU.mem_nhds hpU] with q hq
    exact (eisensteinPartials_eq_tsum s hs j q (hbound q hq).1).2
  exact ⟨(hsum₁.continuousAt (hU.mem_nhds hpU)).congr heq₁.symm,
    (hsum₂.continuousAt (hU.mem_nhds hpU)).congr heq₂.symm⟩
end OAI.CubicEisenstein
