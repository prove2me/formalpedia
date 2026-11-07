-- Prove2me | solution 1 for OAI.QuadraticUnitInvariance.quadratic_unit_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:01:37.363412+00:00
-- url     : https://prove2.me/submissions/7571cb79-f6ea-437f-b081-ccb8a33ab3cc

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
import Theorems.Thm_OAI_QuadraticUnitInvariance_principalNormalizedGauss_three_eq_rayValue
import Theorems.Thm_OAI_GaussGeneratorTransport_principalNormalizedGauss_unit_change


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
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open OAI.QuadraticUnitInvariance
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates
open GaussGeneratorTransport QuadraticGaussRay
namespace OAI.QuadraticUnitInvariance
theorem _root_.solution
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (u : Oˣ) :
    finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) u.val *
      quadraticRayValue (residue (∏ i, p i)) =
        quadraticRayValue (residue (u.val * ∏ i, p i)) := by
  have hn0 : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hn : Ideal.span {∏ i, p i} = ∏ i, Ideal.span {p i} := span_finset_prod _ _
  have hc : Ideal.span {u.val * ∏ i, p i} = ∏ i, Ideal.span {p i} := by
    rw [Ideal.span_singleton_mul_left_unit u.isUnit, hn]
  have h := principalNormalizedGauss_unit_change (fun i => Ideal.span {p i}) hcop hg (fun _ => 3)
    (u.val * ∏ i, p i) (∏ i, p i) hc hn (mul_ne_zero u.ne_zero hn0) hn0 u rfl
  rw [principalNormalizedGauss_three_eq_rayValue _ hcop hg hchar,
    principalNormalizedGauss_three_eq_rayValue _ hcop hg hchar] at h
  exact h.symm
end OAI.QuadraticUnitInvariance
