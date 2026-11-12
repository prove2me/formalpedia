-- Prove2me | solution 1 for OAI.CubicEisenstein.affineDenominator_integral_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:09:29.857205+00:00
-- url     : https://prove2.me/submissions/c41ce898-5744-4e19-83a0-5906e07095fa

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedCuspPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_AffineCuspFourier
import Theorems.Thm_OAI_CubicEisenstein_affineLowerTerm_fourier_integral
import Theorems.Thm_OAI_CubicEisenstein_affineLowerIntegral_sum_translate

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
open Filter MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (h h1 q r k:Eis) (j n:ℕ) (a:PrimaryLower)
    (hq:q≠0) (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hk:3*k=h1+ramifiedAffineParameter j n*a.val)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (hsum:Summable (fun d:PrimaryCoprimeDenominator a=>∫z in periodDomain,
      affineLowerTerm q r z v s a.val d.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))) :
    (∑'d:PrimaryCoprimeDenominator a,∫z in periodDomain,
      affineLowerTerm q r z v s a.val d.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*
        ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
          ((‖eisEmbedding (q*a.val)‖^2:ℝ):ℂ)^(-s)*ramifiedAffineGauss h q r a.val := by
  let e:=(cubicResidueElementEquiv a.val (primaryLower_ne_zero a)).trans (primaryDenominatorEquiv a)
  have hpair:=e.summable_iff.mpr hsum
  change Summable (fun p:CubicUnitResidue a.val×Eis=>∫z in periodDomain,
    affineLowerTerm q r z v s a.val (a.val+3*(GaussianShiftedPartition.representative a.val p.1.val+a.val*p.2))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z)) at hpair
  rw [←e.tsum_eq]
  change (∑'p:CubicUnitResidue a.val×Eis,∫z in periodDomain,
    affineLowerTerm q r z v s a.val (a.val+3*(GaussianShiftedPartition.representative a.val p.1.val+a.val*p.2))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=_
  rw [hpair.tsum_prod]
  have hinner (x:CubicUnitResidue a.val) :
      (∑'m:Eis,∫z in periodDomain,
        affineLowerTerm q r z v s a.val (a.val+3*(GaussianShiftedPartition.representative a.val x.val+a.val*m))*
          ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*
        (((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
          ((‖eisEmbedding (q*a.val)‖^2:ℝ):ℂ)^(-s)*
            ((eisEmbedding (symbol r (a.val+3*GaussianShiftedPartition.representative a.val x.val))*
              eisEmbedding (symbol (a.val+3*GaussianShiftedPartition.representative a.val x.val) a.val))*
                ShortDraftTrace.breveE (ninthCuspFrequency h*
                  eisEmbedding (a.val+3*GaussianShiftedPartition.representative a.val x.val)/eisEmbedding (q*a.val)))) := by
    rw [affineLowerIntegral_sum_translate h h1 q r a.val k _ j n (primaryLower_ne_zero a)
      (primaryLower_primary a) hq hr hh hk v hv s hs,
      affineLowerTerm_fourier_integral q r v hv s _ a.val _ (primaryLower_ne_zero a) hq]
  simp_rw [hinner]
  unfold ramifiedAffineGauss
  simp_rw [mul_assoc]
  rw [tsum_mul_left,tsum_mul_left,tsum_mul_left,tsum_mul_left]
end OAI.CubicEisenstein
