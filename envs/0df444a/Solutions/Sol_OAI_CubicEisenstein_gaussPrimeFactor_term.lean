-- Prove2me | solution 1 for OAI.CubicEisenstein.gaussPrimeFactor_term
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:05:29.645641+00:00
-- url     : https://prove2.me/submissions/754a6206-3d12-4f11-8761-1497151e6733

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BesselMellinTransform
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_TranslatedFourierResidues
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ResidualCuspDecay
import Theorems.Thm_OAI_CubicEisenstein_primeDeleted_generator_coprime
import Theorems.Thm_OAI_CubicEisenstein_primary_pow_congruence
import Theorems.Thm_OAI_CompletedGauss_primaryGenerator_span
import Theorems.Thm_OAI_CubicEisenstein_cubicUnitGaussSum_coprime_product


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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open OAI.CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (s:ℂ) (h:Eis) (n:ℕ) (I:PrimeDeletedIdeal p):
    (Ideal.absNorm (gaussPrimeFactorMap p hp hprimary (n,I)).val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator (gaussPrimeFactorMap p hp hprimary (n,I)).val)=
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^n*cubicUnitGaussSum h (p^n)*
      ((Ideal.absNorm I.val.val:ℂ)^(-s)*cubicUnitGaussSum (h*p^n) (primaryGenerator I.val.val)):=by
  change (Ideal.absNorm ((Ideal.span {p})^n*I.val.val):ℂ)^(-s)*
    cubicUnitGaussSum h (primaryGenerator ((Ideal.span {p})^n*I.val.val))=_
  rw [primaryGenerator_mul,primaryGenerator_pow,primaryGenerator_span p hp.ne_zero hprimary,
    cubicUnitGaussSum_coprime_product h (p^n) (primaryGenerator I.val.val)
      (pow_ne_zero _ hp.ne_zero) I.val.2 (primary_pow_congruence p hprimary n)
      (primaryGenerator_spec I.val.val I.val.2).2 (primeDeleted_generator_coprime p hp I).pow_left,
    map_mul,map_pow,Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  have he:((Ideal.absNorm (Ideal.span {p})^n:ℕ):ℂ)^(-s)=
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^n:=by
    rw [Nat.cast_pow,←Complex.natCast_cpow_natCast_mul,Complex.cpow_nat_mul]
  rw [he]
  ring
end OAI.CubicEisenstein
