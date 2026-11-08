-- Prove2me | solution 1 for OAI.CubicEisenstein.smoothSummand_axisLaplacian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:34:02.821509+00:00
-- url     : https://prove2.me/submissions/997a238e-1f6e-4b8f-bda7-8ff2feb23fc1

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SpatialDerivatives
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_FirstCoreCutoff
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SmoothSummands
import Theorems.Thm_OAI_CubicEisenstein_axisLaplacian_eq_hyperbolicLaplacian
import Theorems.Thm_OAI_CubicEisenstein_complex_row_quadratic_relation
import Theorems.Thm_OAI_CubicEisenstein_embeddedRow_ne_zero
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicLaplacian_const_mul
import Theorems.Thm_OAI_CubicEisenstein_row_denominator_pos
import Theorems.Thm_OAI_CubicEisenstein_spatialHeightPower_eigenfunction


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
theorem _root_.solution (s : ℂ) (r : CuspCosets) (p : SpatialCoordinates) (hv : 0<p 2) :
    axisLaplacian (smoothSummand s r) p = s*(s-2)*smoothSummand s r p := by
  unfold smoothSummand rowSmoothPower
  rw [axisLaplacian_eq_hyperbolicLaplacian
    (fun x y v => (cosetCharacter r)⁻¹ *
      spatialHeightPower s (Complex.normSq (embeddedRow r 0))
        ((embeddedRow r 0*star (embeddedRow r 1)).re)
        (-(embeddedRow r 0*star (embeddedRow r 1)).im)
        (Complex.normSq (embeddedRow r 1)) x y v) p,
    hyperbolicLaplacian_const_mul,spatialHeightPower_eigenfunction]
  · ring
  · exact complex_row_quadratic_relation _ _
  · exact hv.ne'
  · exact (row_denominator_pos _ (embeddedRow_ne_zero r) p hv).ne'
end OAI.CubicEisenstein
