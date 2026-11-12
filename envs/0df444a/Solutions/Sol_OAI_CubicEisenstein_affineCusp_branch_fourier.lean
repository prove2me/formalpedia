-- Prove2me | solution 1 for OAI.CubicEisenstein.affineCusp_branch_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:14:56.120001+00:00
-- url     : https://prove2.me/submissions/9b7fc317-7edd-491c-8a87-84cb4dc8b802

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedCuspPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_AffineCuspFourier
import Theorems.Thm_OAI_CubicEisenstein_affineDenominator_integral_formula
import Theorems.Thm_OAI_CubicEisenstein_affineCuspFrequency_lift
import Theorems.Thm_OAI_CubicEisenstein_affineCusp_norm_factor
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_norm_sq_eq_absNorm_span
import Theorems.Thm_OAI_CubicEisenstein_ramifiedAffineGauss_eq_unramified


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
theorem _root_.solution (h h1 q r:Eis) (j n:ℕ)
    (hq:q≠0) (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hfreq:(3:Eis)∣h1+ramifiedAffineParameter j n)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (hsum:Summable (fun p:UnitLowerData=>∫z in periodDomain,
      affineLowerTerm q r z v s p.1.val p.2.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))) :
    (∑'p:UnitLowerData,∫z in periodDomain,
      affineLowerTerm q r z v s p.1.val p.2.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*((‖eisEmbedding q‖^2:ℝ):ℂ)^(-s)*
        ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
          ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
            unramifiedCubicGaussSeries s (3*r^2*h1) := by
  rw [hsum.tsum_sigma]
  have ha (a:PrimaryLower):
      (∑'d:PrimaryCoprimeDenominator a,∫z in periodDomain,
        affineLowerTerm q r z v s a.val d.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ((Ideal.absNorm (Ideal.span {q}):ℂ)*((‖eisEmbedding q‖^2:ℝ):ℂ)^(-s)*
        ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
          ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q))*
        (((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s)*cubicUnitGaussSum (3*r^2*h1) a.val) := by
    obtain ⟨k,hk⟩:=affineCuspFrequency_lift h1 j n a hfreq
    rw [affineDenominator_integral_formula h h1 q r k j n a hq hr hh hk v hv s hs
      (hsum.sigma_factor a),ramifiedAffineGauss_eq_unramified h h1 q r a.val k j n
        (primaryLower_ne_zero a) (primaryLower_primary a) hq hr hh hk,
      affineCusp_norm_factor]
    ring
  simp_rw [ha]
  rw [tsum_mul_left]
  congr 1
  rw [←primaryLowerIdealEquiv.symm.tsum_eq,unramifiedCubicGaussSeries]
  apply tsum_congr
  intro I
  change ((‖eisEmbedding (CompletedGauss.primaryGenerator I.val)‖^2:ℝ):ℂ)^(-s)*
    cubicUnitGaussSum (3*r^2*h1) (CompletedGauss.primaryGenerator I.val)=_
  rw [eisEmbedding_norm_sq_eq_absNorm_span,(CompletedGauss.primaryGenerator_spec I.val I.2).1,
    Complex.ofReal_natCast]
end OAI.CubicEisenstein
