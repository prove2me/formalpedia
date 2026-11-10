-- Prove2me | solution 1 for OAI.CubicEisenstein.fullCuspProfileField_laplacian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:18:55.715837+00:00
-- url     : https://prove2.me/submissions/3014ec39-08c5-44f7-8f71-389b972bc59f

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectedBranches
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspHeight
import Theorems.Thm_OAI_CubicEisenstein_fullCuspRow_ne_zero
import Theorems.Thm_OAI_CubicEisenstein_fullCuspRows_locally_finite
import Theorems.Thm_OAI_CubicEisenstein_fullCuspProfile_row_laplacian
import Theorems.Thm_OAI_CubicEisenstein_axisLaplacian_congr_eventuallyEq
import Theorems.Thm_OAI_CubicEisenstein_axisLaplacian_finset_sum
import Theorems.Thm_OAI_CubicEisenstein_rowProfile_axis_derivatives


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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups
namespace OAI.CubicEisenstein
theorem _root_.solution (F : ℝ→ℝ) (hF : ContDiff ℝ ∞ F)
    (hzero : ∀v≤1,F v=0) (hLzero : ∀v≤1,positiveHeightLaplacian F v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    -axisLaplacian (fun q => (fullCuspProfileField F q:ℂ)) p=
      (fullCuspProfileField (positiveHeightLaplacian F) p:ℂ) := by
  obtain ⟨T,hT⟩ := fullCuspRows_locally_finite p hp
  have he : (fun q => (fullCuspProfileField F q:ℂ)) =ᶠ[𝓝 p]
      (fun q => ∑x∈T,(F (rowHeight (fullCuspRow x) q):ℂ)) := by
    filter_upwards [hT] with q hq
    have hh : fullCuspProfileField F q=∑x∈T,F (rowHeight (fullCuspRow x) q) :=
      tsum_eq_sum (fun x hx => hzero _ (hq x hx).le)
    rw [hh]
    push_cast
    rfl
  have hval : fullCuspProfileField (positiveHeightLaplacian F) p=
      ∑x∈T,positiveHeightLaplacian F (rowHeight (fullCuspRow x) p) :=
    tsum_eq_sum (fun x hx => hLzero _ (hT.self_of_nhds x hx).le)
  have hreg : ∀x∈T,∀q,0<q 2→∀j : Fin 3,
      DifferentiableAt ℝ (axisSlice (fun z => (F (rowHeight (fullCuspRow x) z):ℂ)) q j) (q j) ∧
      DifferentiableAt ℝ (deriv (axisSlice (fun z => (F (rowHeight (fullCuspRow x) z):ℂ)) q j)) (q j) := by
    intro x hx q hq j
    have hd := rowProfile_axis_derivatives (fun v => (F v:ℂ))
      (fun v hv => Complex.ofRealCLM.contDiff.contDiffAt.comp v hF.contDiffAt)
      (fullCuspRow x) (fullCuspRow_ne_zero x) q hq j
    exact ⟨hd.1.differentiableAt,hd.2.differentiableAt⟩
  rw [axisLaplacian_congr_eventuallyEq _ _ p he,axisLaplacian_finset_sum T _ hreg p hp,hval]
  rw [←Finset.sum_neg_distrib]
  push_cast
  exact Finset.sum_congr rfl (fun x hx => fullCuspProfile_row_laplacian F hF x p hp)
end OAI.CubicEisenstein
