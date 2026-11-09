-- Prove2me | solution 1 for OAI.CubicEisenstein.mobius_upperPoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T05:02:12.71957+00:00
-- url     : https://prove2.me/submissions/ae00608e-78b9-4cfd-9045-401f25c250c3

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ArithmeticBins
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_HyperbolicVolume
import Theorems.Thm_OAI_CubicEisenstein_matrix_point_coordinates
import Theorems.Thm_OAI_CubicEisenstein_matrixHorizontal_eq_cross_height
import Theorems.Thm_OAI_CubicEisenstein_matrixCross_upperSection
import Theorems.Thm_OAI_CubicEisenstein_upperPoint_congr
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicHeight_action_upperPoint


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
theorem _root_.solution (g : SL(2,ℂ)) (z : ℂ) (v : ℝ) (hv : 0<v) :
    g • upperPoint z v hv=
      upperPoint
        (((g 0 0*z+g 0 1)*star (g 1 0*z+g 1 1)+g 0 0*star (g 1 0)*(v:ℂ)^2)/
          ((‖g 1 0*z+g 1 1‖^2+‖g 1 0‖^2*v^2:ℝ):ℂ))
        (v/(‖g 1 0*z+g 1 1‖^2+‖g 1 0‖^2*v^2))
        (div_pos hv (mobius_denominator_pos g z v hv)) := by
  have hh : liftedHeight (g*upperSection z v hv)=
      v/(‖g 1 0*z+g 1 1‖^2+‖g 1 0‖^2*v^2) :=
    hyperbolicHeight_action_upperPoint g z v hv
  change (QuotientGroup.mk (g*upperSection z v hv) : HyperbolicSpace)=_
  rw [matrix_point_coordinates]
  apply upperPoint_congr _ _ _ hh
  rw [matrixHorizontal_eq_cross_height,matrixCross_upperSection,hh,Complex.ofReal_div]
  have hvc : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  field_simp
end OAI.CubicEisenstein
