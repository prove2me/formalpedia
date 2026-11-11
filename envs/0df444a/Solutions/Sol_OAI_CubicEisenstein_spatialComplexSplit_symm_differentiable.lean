-- Prove2me | solution 1 for OAI.CubicEisenstein.spatialComplexSplit_symm_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T03:26:41.192113+00:00
-- url     : https://prove2.me/submissions/0fbf12b8-a8bd-4416-991a-1ecc0ed3351a

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SourceBesselExpansion
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_InverseCuspCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ReflectedCuspMellin
import Theorems.Thm_OAI_CubicEisenstein_quadraticHeightDenominator_continuous
import Theorems.Thm_OAI_CubicEisenstein_spatialComplexSplit_symm_eq
attribute [local fun_prop] OAI.CubicEisenstein.quadraticHeightDenominator_continuous



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
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution : Differentiable ℝ spatialComplexSplit.symm := by
  change Differentiable ℝ (fun q : ℝ × ℂ => spatialComplexSplit.symm q)
  simp_rw [spatialComplexSplit_symm_eq]
  have hlin := (WithLp.linearEquiv 2 ℝ (Fin 3→ℝ)).symm.toContinuousLinearMap.differentiable
  have hcoords : Differentiable ℝ (fun q : ℝ × ℂ => ![q.2.re,q.2.im,q.1]) := by
    apply differentiable_pi.mpr
    intro j
    fin_cases j
    · change Differentiable ℝ (fun q : ℝ × ℂ => q.2.re)
      fun_prop
    · change Differentiable ℝ (fun q : ℝ × ℂ => q.2.im)
      fun_prop
    · change Differentiable ℝ (fun q : ℝ × ℂ => q.1)
      fun_prop
  exact hlin.comp hcoords
end OAI.CubicEisenstein
