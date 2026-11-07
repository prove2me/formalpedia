-- Prove2me | solution 1 for OAI.QuadraticUnitInvariance.quadratic_pair_unit_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:08:59.62525+00:00
-- url     : https://prove2.me/submissions/07c70fd5-1c58-4b34-bbb1-5fec1cbd4e16

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
import Theorems.Thm_OAI_QuadraticUnitInvariance_finiteSexticRow_three_star
import Theorems.Thm_OAI_QuadraticUnitInvariance_quadratic_unit_value_eq_of_same_ray
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSexticRow_mul
import Theorems.Thm_OAI_GaussGeneratorTransport_finiteSexticRow_unit_mul_star


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
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (q : κ → O) (hq : ∀ i, q i ≠ 0) [∀ i, (Ideal.span {q i}).IsMaximal]
    (hcopq : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {q i})))
    (hgq : ∀ i, lambda ∉ Ideal.span {q i})
    (hcharq : ∀ i, ringChar (O ⧸ Ideal.span {q i}) ≠ 2)
    (hray : residue (∏ i, p i) = residue (∏ i, q i)) (u : Oˣ) (z : O) :
    finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) (u.val * z) *
      finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) (u.val * z) =
    finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) z *
      finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) z := by
  have hu := quadratic_unit_value_eq_of_same_ray p hp hcop hg hchar q hq hcopq hgq hcharq hray u
  have hs := finiteSexticRow_unit_mul_star (fun i => Ideal.span {q i}) hgq (fun _ => 3) u
  rw [finiteSexticRow_three_star] at hs
  rw [finiteSexticRow_mul, finiteSexticRow_mul, hu]
  calc
    _ = (finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) u.val *
        finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) u.val) *
      (finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) z *
        finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) z) := by ring
    _ = _ := by rw [hs, one_mul]
end OAI.QuadraticUnitInvariance
