-- Prove2me | solution 1 for OAI.QuadraticUnitInvariance.quadratic_unit_value_eq_of_same_ray
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:06:01.477146+00:00
-- url     : https://prove2.me/submissions/609af3d3-2566-46f0-9430-240c2e7ab0a1

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
import Theorems.Thm_OAI_QuadraticUnitInvariance_quadratic_unit_phase
import Theorems.Thm_OAI_ActualEisensteinCoordinates_residue_mul
import Theorems.Thm_OAI_FiniteGaussPhase_norm_canonicalProductGauss
import Theorems.Thm_OAI_QuadraticGaussRay_canonicalProductGauss_three_eq_rayValue


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
    (hray : residue (∏ i, p i) = residue (∏ i, q i)) (u : Oˣ) :
    finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) u.val =
      finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) u.val := by
  have hne : quadraticRayValue (residue (∏ i, p i)) ≠ 0 := by
    rw [← canonicalProductGauss_three_eq_rayValue p hp hcop hg hchar]
    exact norm_ne_zero_iff.mp (by rw [norm_canonicalProductGauss p hp hcop hg hchar
      (fun _ => 3) (fun _ => by decide) (fun _ => by decide)]; norm_num)
  apply mul_right_cancel₀ hne
  rw [quadratic_unit_phase p hp hcop hg hchar, hray,
    quadratic_unit_phase q hq hcopq hgq hcharq, residue_mul, residue_mul, hray]
end OAI.QuadraticUnitInvariance
