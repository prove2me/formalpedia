-- Prove2me | solution 1 for OAI.CubicEisenstein.actualHeightPower_eigenfunction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:14:16.167207+00:00
-- url     : https://prove2.me/submissions/e3251834-9dc9-4089-9767-f3721401be65

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_TruncatedSecondTransfer
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_TwistedProfiles
import Theorems.Thm_OAI_CubicEisenstein_spatialHeightPower_eigenfunction
import Theorems.Thm_OAI_CubicEisenstein_complex_row_quadratic_relation
import Theorems.Thm_OAI_CubicEisenstein_heightDenominator_eq_quadratic
import Theorems.Thm_OAI_CubicEisenstein_actualHeightPower_eq_spatial
import Theorems.Thm_OAI_CubicEisenstein_heightDenominator_pos


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
open scoped BigOperators Classical SchwartzMap ContDiff
open Filter
open scoped BigOperators Classical Topology
open OAI.CubicEisenstein
namespace OAI.CubicEisenstein
theorem _root_.solution (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (x y v : ℝ) (hv : 0<v) :
    hyperbolicLaplacian (actualHeightPower s u) x y v =
      s*(s-2)*actualHeightPower s u x y v := by
  let A := Complex.normSq (u 0)
  let B := (u 0*star (u 1)).re
  let C := -(u 0*star (u 1)).im
  let D := Complex.normSq (u 1)
  have heq (x' y' v' : ℝ) (hv' : 0<v') :
      actualHeightPower s u x' y' v' = spatialHeightPower s A B C D x' y' v' :=
    actualHeightPower_eq_spatial s u hu x' y' v' hv'
  have hxeq : (fun t => actualHeightPower s u t y v) =
      (fun t => spatialHeightPower s A B C D t y v) := funext fun t => heq t y v hv
  have hyeq : (fun t => actualHeightPower s u x t v) =
      (fun t => spatialHeightPower s A B C D x t v) := funext fun t => heq x t v hv
  have hveq : actualHeightPower s u x y =ᶠ[𝓝 v] spatialHeightPower s A B C D x y := by
    filter_upwards [isOpen_Ioi.mem_nhds (show v ∈ Set.Ioi 0 from hv)] with t ht
    exact heq x y t ht
  have hq : quadraticHeightDenominator A B C D x y v≠0 := by
    rw [← heightDenominator_eq_quadratic]
    exact (heightDenominator_pos _ _ hv u hu).ne'
  rw [heq x y v hv]
  convert spatialHeightPower_eigenfunction s A B C D x y v
    (complex_row_quadratic_relation (u 0) (u 1)) hv.ne' hq using 1
  unfold hyperbolicLaplacian
  rw [hxeq,hyeq,hveq.deriv_eq,hveq.deriv.deriv_eq]
end OAI.CubicEisenstein
