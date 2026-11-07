-- Prove2me | solution 1 for OAI.FiniteRayExpansion.unitTensorCoeff_sum_norm_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:31:51.142923+00:00
-- url     : https://prove2.me/submissions/686666c1-3321-40a8-96d9-51f6ffc79e48

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_IdealMobius
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedExpansion
import Theorems.Thm_OAI_FiniteRayExpansion_unitFourierCoeff_sum_norm_le_sum

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
open scoped BigOperators Classical
open OAI.FiniteRayExpansion
variable {R : Type*} [CommRing R] [Fintype R]
attribute [local instance] OAI.FiniteRayExpansion._p2m_local_instance_47d1e46724_359
namespace OAI.FiniteRayExpansion
theorem _root_.solution (f : Rˣ → Rˣ → ℂ) :
    (∑ χ : MulChar R ℂ, ∑ η : MulChar R ℂ, ‖unitTensorCoeff f χ η‖) ≤
      ∑ u : Rˣ, ∑ v : Rˣ, ‖f u v‖ := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ η : MulChar R ℂ, ∑ u : Rˣ, ‖unitFourierCoeff (f u) η‖ :=
      Finset.sum_le_sum (fun η _ => unitFourierCoeff_sum_norm_le_sum (fun u => unitFourierCoeff (f u) η))
    _ = ∑ u : Rˣ, ∑ η : MulChar R ℂ, ‖unitFourierCoeff (f u) η‖ := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun u _ => unitFourierCoeff_sum_norm_le_sum (f u))
end OAI.FiniteRayExpansion
