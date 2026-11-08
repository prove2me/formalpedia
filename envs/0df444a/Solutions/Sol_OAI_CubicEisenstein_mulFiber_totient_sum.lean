-- Prove2me | solution 1 for OAI.CubicEisenstein.mulFiber_totient_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:34:02.307473+00:00
-- url     : https://prove2.me/submissions/607a30fc-96f7-472c-8aca-2e3a6e09ff25

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ConjugateProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_RamifiedNormWeights
import Theorems.Thm_OAI_CubicEisenstein_idealTotient_moebius

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
open OAI.CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid CompletedGauss
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)
namespace OAI.CubicEisenstein
theorem _root_.solution (B : Ideal O) (hB : B ≠ 0) :
    (∑' p : MulFiber B,(moebius p.1.1:ℂ)*(Ideal.absNorm p.1.2:ℂ))=(idealTotient B:ℂ) := by
  let e := mulFiberDivisorEquiv B hB
  have hp (p : MulFiber B) :
      (moebius p.1.1:ℂ)*(Ideal.absNorm p.1.2:ℂ)=
        (Ideal.absNorm B:ℂ)*((moebius p.1.1:ℂ)/(Ideal.absNorm p.1.1:ℂ)) := by
    have hI : p.1.1 ≠ 0 := by
      intro hz
      have hh := p.2
      rw [hz,zero_mul] at hh
      exact hB hh.symm
    have hn : (Ideal.absNorm p.1.1:ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
    have heq : (Ideal.absNorm B:ℂ)=(Ideal.absNorm p.1.1:ℂ)*(Ideal.absNorm p.1.2:ℂ) := by
      calc
        _ = (Ideal.absNorm (p.1.1*p.1.2):ℂ) := congrArg (fun I => (Ideal.absNorm I:ℂ)) p.2.symm
        _ = _ := by rw [map_mul,Nat.cast_mul]
    rw [heq]
    field_simp
  calc
    _ = ∑' p : MulFiber B,(Ideal.absNorm B:ℂ)*
        ((moebius p.1.1:ℂ)/(Ideal.absNorm p.1.1:ℂ)) := tsum_congr hp
    _ = (Ideal.absNorm B:ℂ)*
        ∑' D : {D : Ideal O // D ∈ idealDivisors B},
          ((moebius D.1:ℂ)/(Ideal.absNorm D.1:ℂ)) := by
      rw [← tsum_mul_left]
      exact e.tsum_eq (fun D => (Ideal.absNorm B:ℂ)*((moebius D.1:ℂ)/(Ideal.absNorm D.1:ℂ)))
    _ = (Ideal.absNorm B:ℂ)*
        ∑ D ∈ idealDivisors B,((moebius D:ℂ)/(Ideal.absNorm D:ℂ)) := by
      rw [tsum_fintype]
      apply congrArg (fun z : ℂ => (Ideal.absNorm B:ℂ)*z)
      exact (Finset.sum_subtype (idealDivisors B) (fun _ => Iff.rfl)
        (fun D => (moebius D:ℂ)/(Ideal.absNorm D:ℂ))).symm
    _ = _ := (idealTotient_moebius B hB).symm
end OAI.CubicEisenstein
