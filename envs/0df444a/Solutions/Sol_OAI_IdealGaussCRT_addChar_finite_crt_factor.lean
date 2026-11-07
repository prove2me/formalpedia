-- Prove2me | solution 1 for OAI.IdealGaussCRT.addChar_finite_crt_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:59:20.220481+00:00
-- url     : https://prove2.me/submissions/43ff4250-cc89-4c18-bbc5-10a70a685ac1

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SecondPoissonScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_EisensteinLattice
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
namespace OAI
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
namespace EisensteinSchwartzPoisson
section
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace
end
section
open scoped RealInnerProductSpace
end
section
open MeasureTheory EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace
end
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff
end EisensteinSchwartzPoisson
open scoped BigOperators Classical
namespace IdealGaussCRT
private theorem addChar_finite_sum {ι T : Type*} [AddCommMonoid T]
    (ψ : AddChar T ℂ) (s : Finset ι) (f : ι → T) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, AddChar.map_add_eq_mul, ih]
end IdealGaussCRT
end
end OAI
end

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
open OAI.IdealGaussCRT
namespace OAI.IdealGaussCRT
theorem _root_.solution {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, CommRing (R i)]
    (e : T ≃+* ∀ i, R i) (ψ : AddChar T ℂ) (x : T) :
    ψ x = ∏ i, coordinateAddChar R e ψ i (e x i) := by
  classical
  have hx : (∑ i, e.symm (Pi.single i (e x i))) = x := by
    rw [← map_sum, Finset.univ_sum_single, e.symm_apply_apply]
  calc
    ψ x = ψ (∑ i, e.symm (Pi.single i (e x i))) := congrArg ψ hx.symm
    _ = ∏ i, ψ (e.symm (Pi.single i (e x i))) := addChar_finite_sum ψ _ _
    _ = _ := rfl
end OAI.IdealGaussCRT
