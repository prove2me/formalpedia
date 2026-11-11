-- Prove2me | solution 1 for OAI.CubicEisenstein.ramified_arithmetic_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:45:08.640083+00:00
-- url     : https://prove2.me/submissions/4d4b6bf5-d384-407e-b693-9c1bb4d03d18

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_GaussFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_RamifiedGaussSeries
import Theorems.Thm_OAI_CubicEisenstein_ramified_arithmetic_support
import Theorems.Thm_OAI_CubicEisenstein_ramifiedElement_absNorm
import Theorems.Thm_OAI_CubicEisenstein_three_absNorm

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
open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (h : Eis) (hh : h≠0) (u : Eisˣ)
    (n : ℕ) (hn : 2≤n) (hA : arithmeticResidueSum h (u.val*lambda^n)≠0) :
    3^n≤9*Ideal.absNorm (Ideal.span {h}) := by
  have hI:(Ideal.span {h}:Ideal Eis)≠0:=Ideal.span_singleton_eq_bot.not.mpr hh
  have hN:0<Ideal.absNorm (Ideal.span {h}):=
    Nat.pos_of_ne_zero (fun hz=>hI (Ideal.absNorm_eq_zero_iff.mp hz))
  apply Nat.le_of_dvd (by positivity)
  obtain ⟨v,hv⟩:=ramified_arithmetic_support h u n hn hA
  refine ⟨Ideal.absNorm (Ideal.span {v}),?_⟩
  calc
    9*Ideal.absNorm (Ideal.span {h})=Ideal.absNorm (Ideal.span {(3:Eis)*h}):=by
      rw [←Ideal.span_singleton_mul_span_singleton,map_mul,three_absNorm]
    _=Ideal.absNorm (Ideal.span {(u.val*lambda^n)*v}):=by rw [hv]
    _=3^n*Ideal.absNorm (Ideal.span {v}):=by
      rw [←Ideal.span_singleton_mul_span_singleton,map_mul,ramifiedElement_absNorm]
end OAI.CubicEisenstein
