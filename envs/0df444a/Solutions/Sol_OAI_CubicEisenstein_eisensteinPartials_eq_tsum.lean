-- Prove2me | solution 1 for OAI.CubicEisenstein.eisensteinPartials_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T15:12:04.136208+00:00
-- url     : https://prove2.me/submissions/221ef16d-23bf-48f7-a601-28c207b54fd2

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_GreenIdentity
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LogarithmicTargets
import Theorems.Thm_OAI_CubicEisenstein_smoothFirstCoefficient_eq_deriv
import Theorems.Thm_OAI_CubicEisenstein_smoothSecondCoefficient_eq_deriv
import Theorems.Thm_OAI_CubicEisenstein_axisSlice_eventuallyEq_of_positive
import Theorems.Thm_OAI_CubicEisenstein_eisenstein_axis_termwise
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
theorem _root_.solution (s : ℂ) (hs : 2<s.re) (j : Fin 3)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    eisensteinFirstPartial s j p=(∑'r,smoothFirstCoefficient s r j p) ∧
    eisensteinSecondPartial s j p=(∑'r,smoothSecondCoefficient s r j p) := by
  have ht := eisenstein_axis_termwise s hs p hv j
  have heq := axisSlice_eventuallyEq_of_positive (upperEisensteinField s) (smoothEisenstein s)
    (fun q hq => upperEisensteinField_eq_smooth s q hq) p hv j
  constructor
  · unfold eisensteinFirstPartial
    rw [heq.deriv_eq,ht.2.2.1.deriv]
    exact tsum_congr (fun r => (smoothFirstCoefficient_eq_deriv _ _ _ _ hv).symm)
  · unfold eisensteinSecondPartial
    rw [heq.deriv.deriv_eq,ht.2.2.2.deriv]
    exact tsum_congr (fun r => (smoothSecondCoefficient_eq_deriv _ _ _ _ hv).symm)
end OAI.CubicEisenstein
