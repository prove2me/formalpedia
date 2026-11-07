-- Prove2me | solution 1 for OAI.IdealGaussCRT.coordinateAddChar_isPrimitive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:05:49.466651+00:00
-- url     : https://prove2.me/submissions/7ee95e5d-e936-4031-822e-e8c27b7fc70d

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticRadialPoisson
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_IdealGenerators
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
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
open scoped BigOperators Classical
open scoped BigOperators Classical
open OAI.IdealGaussCRT
namespace OAI.IdealGaussCRT
theorem _root_.solution {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, CommRing (R i)]
    (e : T ≃+* ∀ i, R i) (ψ : AddChar T ℂ) (hψ : ψ.IsPrimitive) (i : ι) :
    (coordinateAddChar R e ψ i).IsPrimitive := by
  classical
  intro a ha hshift
  let b : T := e.symm (Pi.single i a)
  have hb : b ≠ 0 := by
    intro hz
    have hh := congrArg (fun z : T => e z i) hz
    exact ha (by simpa [b] using hh)
  apply hψ hb
  ext x
  change ψ (b * x) = 1
  have hx := congrArg (fun φ : AddChar (R i) ℂ => φ (e x i)) hshift
  change ψ (e.symm (Pi.single i (a * e x i))) = 1 at hx
  have hvec : Pi.single i a * e x = Pi.single i (a * e x i) := by
    funext j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Pi.single_eq_of_ne (Ne.symm hij)]
  have hprod : b * x = e.symm (Pi.single i (a * e x i)) := by
    apply e.injective
    rw [map_mul]
    simp only [b, e.apply_symm_apply]
    exact hvec
  rw [hprod]
  exact hx
end OAI.IdealGaussCRT
