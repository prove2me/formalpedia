-- Prove2me | solution 1 for OAI.CubicEisenstein.eisenstein_axis_termwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:44:11.643141+00:00
-- url     : https://prove2.me/submissions/bc450452-773a-4510-a7ea-a51fb65bdcb1

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SpatialDerivatives
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_FirstCoreCutoff
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SmoothSummands
import Theorems.Thm_OAI_CubicEisenstein_axis_summable_derivative_bounds
import Theorems.Thm_OAI_CubicEisenstein_hasDerivAt_deriv_tsum_of_bounds
import Theorems.Thm_OAI_CubicEisenstein_smooth_axis_deriv_differentiable_at
import Theorems.Thm_OAI_CubicEisenstein_smooth_axis_differentiable_at


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
open OAI.CubicEisenstein
open Filter
open scoped BigOperators Classical Topology Matrix
namespace OAI.CubicEisenstein
theorem _root_.solution (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    Summable (fun r => deriv (axisSlice (smoothSummand s r) p j) (p j)) ∧
    Summable (fun r => deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j)) ∧
    HasDerivAt (axisSlice (smoothEisenstein s) p j)
      (∑'r,deriv (axisSlice (smoothSummand s r) p j) (p j)) (p j) ∧
    HasDerivAt (deriv (axisSlice (smoothEisenstein s) p j))
      (∑'r,deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j)) (p j) := by
  obtain ⟨ε,hε,M₀,M₁,M₂,hM₀,hM₁,hM₂,hbound⟩ := axis_summable_derivative_bounds s hs p hv j
  have hx : p j ∈ Metric.ball (p j) ε := Metric.mem_ball_self hε
  have hs₀ : Summable (fun r => axisSlice (smoothSummand s r) p j (p j)) :=
    Summable.of_norm_bounded hM₀ (fun r => ((hbound (p j) hx).2 r).1)
  have hs₁ : Summable (fun r => deriv (axisSlice (smoothSummand s r) p j) (p j)) :=
    Summable.of_norm_bounded hM₁ (fun r => ((hbound (p j) hx).2 r).2.1)
  have hs₂ : Summable (fun r => deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j)) :=
    Summable.of_norm_bounded hM₂ (fun r => ((hbound (p j) hx).2 r).2.2)
  have hd₁ (r : CuspCosets) (t : ℝ) (ht : t∈Metric.ball (p j) ε) :
      DifferentiableAt ℝ (axisSlice (smoothSummand s r) p j) t :=
    smooth_axis_differentiable_at s r p j t (hbound t ht).1
  have hd₂ (r : CuspCosets) (t : ℝ) (ht : t∈Metric.ball (p j) ε) :
      DifferentiableAt ℝ (deriv (axisSlice (smoothSummand s r) p j)) t :=
    smooth_axis_deriv_differentiable_at s r p j t (hbound t ht).1
  refine ⟨hs₁,hs₂,?_,?_⟩
  · exact hasDerivAt_tsum_of_isPreconnected hM₁ Metric.isOpen_ball Metric.isPreconnected_ball
      (fun r t ht => (hd₁ r t ht).hasDerivAt) (fun r t ht => ((hbound t ht).2 r).2.1) hx hs₀ hx
  · exact hasDerivAt_deriv_tsum_of_bounds (fun r => axisSlice (smoothSummand s r) p j)
      M₁ M₂ _ (p j) Metric.isOpen_ball Metric.isPreconnected_ball hx hM₁ hM₂ hd₁ hd₂
      (fun r t ht => ((hbound t ht).2 r).2.1) (fun r t ht => ((hbound t ht).2 r).2.2) hs₀
end OAI.CubicEisenstein
