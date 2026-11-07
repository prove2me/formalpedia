-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.fourier_comp_linearEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:59:16.680606+00:00
-- url     : https://prove2.me/submissions/74b45288-0cb6-4e56-8302-dce6429a8783

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SecondPoissonScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_EisensteinLattice
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_integral_comp_linearEquiv
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_inner_linear_dual
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
open OAI.EisensteinSchwartzPoisson
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace
namespace OAI.EisensteinSchwartzPoisson
theorem _root_.solution (A : ℂ ≃L[ℝ] ℂ) (f : ℂ → ℂ) (w : ℂ) :
    𝓕 (f ∘ A) w = inverseJacobian A • 𝓕 f (dualMap A w) := by
  let H : ℂ → ℂ := fun z => Real.fourierChar (-inner ℝ z (dualMap A w)) • f z
  calc
    𝓕 (f ∘ A) w = ∫ x : ℂ, H (A x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [H, inner_linear_dual, Function.comp_apply]
        rfl
    _ = inverseJacobian A • ∫ z : ℂ, H z := integral_comp_linearEquiv A H
    _ = inverseJacobian A • 𝓕 f (dualMap A w) := rfl
end OAI.EisensteinSchwartzPoisson
