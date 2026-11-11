-- Prove2me | solution 1 for OAI.CubicEisenstein.unramifiedCubicGaussSeries_prime_reindex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:17:13.967264+00:00
-- url     : https://prove2.me/submissions/c1ed4949-07f8-422a-a46a-f1b836071a42

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BesselMellinTransform
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_TranslatedFourierResidues
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ResidualCuspDecay
import Theorems.Thm_OAI_CubicEisenstein_unramifiedCubicGaussSeries_summable_norm
import Theorems.Thm_OAI_CubicEisenstein_gaussPrimeFactor_term

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
theorem _root_.solution (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis):
    unramifiedCubicGaussSeries s h=
      ∑'n:ℕ,((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^n*cubicUnitGaussSum h (p^n)*
        unramifiedPrimeDeletedSeries p s (h*p^n):=by
  have hsum:Summable (fun I:GoodIdeal=>(Ideal.absNorm I.val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator I.val)):=
    (unramifiedCubicGaussSeries_summable_norm s hs h).of_norm
  have hpull:=(gaussPrimeFactorEquiv p hp hprimary).summable_iff.mpr hsum
  change Summable (fun q:ℕ×PrimeDeletedIdeal p=>
    (Ideal.absNorm (gaussPrimeFactorMap p hp hprimary q).val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator (gaussPrimeFactorMap p hp hprimary q).val)) at hpull
  rw [unramifiedCubicGaussSeries,←(gaussPrimeFactorEquiv p hp hprimary).tsum_eq]
  change (∑'q:ℕ×PrimeDeletedIdeal p,
    (Ideal.absNorm (gaussPrimeFactorMap p hp hprimary q).val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator (gaussPrimeFactorMap p hp hprimary q).val))=_
  rw [hpull.tsum_prod]
  apply tsum_congr
  intro n
  change (∑'I:PrimeDeletedIdeal p,(Ideal.absNorm (gaussPrimeFactorMap p hp hprimary (n,I)).val:ℂ)^(-s)*
    cubicUnitGaussSum h (primaryGenerator (gaussPrimeFactorMap p hp hprimary (n,I)).val))=_
  simp_rw [gaussPrimeFactor_term p hp hprimary s h n]
  exact tsum_mul_left
end OAI.CubicEisenstein
