-- Prove2me | solution 1 for OAI.CubicEisenstein.unitDenominator_integral_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:05:54.690208+00:00
-- url     : https://prove2.me/submissions/81fd1771-17b6-4140-8ec6-c39919156202

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ConjugateCuspProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspDilation
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_ResiduesModThree
import Theorems.Thm_OAI_CubicEisenstein_hasSum_unitLowerIntegrals
import Theorems.Thm_OAI_CubicEisenstein_unitLowerTerm_fourier_integral
import Theorems.Thm_OAI_CubicEisenstein_unitLowerIntegral_sum_translate
import Theorems.Thm_OAI_CubicEisenstein_SubexponentialBesselCoefficients_summable
import Theorems.Thm_OAI_CubicEisenstein_unitCuspFrequency_lift


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
open scoped Classical MatrixGroups
open Filter MeasureTheory
open scoped BigOperators Classical
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (u : Eisˣ) (j : ℕ) (hu : (u:Eis)=omega^j)
    (h : Eis) (hh : UnitCuspFrequency h u j) (a : PrimaryLower)
    (v : ℝ) (hv : 0<v) (s : ℂ) (hs : 2<s.re) :
    (∑'d:PrimaryCoprimeDenominator a,unitLowerIntegral u v s (ninthCuspFrequency h) a.val d.val.val)=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s)*unitLowerGauss h u a.val := by
  obtain ⟨k,hk⟩ := unitCuspFrequency_lift h a.val u j (primaryLower_primary a) hh
  let e := (cubicResidueElementEquiv a.val (primaryLower_ne_zero a)).trans (primaryDenominatorEquiv a)
  have hf : Summable (fun d:PrimaryCoprimeDenominator a =>
      unitLowerIntegral u v s (ninthCuspFrequency h) a.val d.val.val) :=
    (hasSum_unitLowerIntegrals u v hv s (ninthCuspFrequency h) hs).summable.sigma_factor a
  have hsum := e.summable_iff.mpr hf
  change Summable (fun q:CubicUnitResidue a.val×Eis =>
    unitLowerIntegral u v s (ninthCuspFrequency h) a.val
      (a.val+3*(GaussianShiftedPartition.representative a.val q.1.val+a.val*q.2))) at hsum
  rw [←e.tsum_eq]
  change (∑'q:CubicUnitResidue a.val×Eis,
    unitLowerIntegral u v s (ninthCuspFrequency h) a.val
      (a.val+3*(GaussianShiftedPartition.representative a.val q.1.val+a.val*q.2)))=_
  rw [hsum.tsum_prod]
  have hinner (r:CubicUnitResidue a.val) :
      (∑'n:Eis,unitLowerIntegral u v s (ninthCuspFrequency h) a.val
        (a.val+3*(GaussianShiftedPartition.representative a.val r.val+a.val*n)))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s)*
          ((eisEmbedding (symbol (u:Eis) (a.val+3*GaussianShiftedPartition.representative a.val r.val))*
            eisEmbedding (symbol (a.val+3*GaussianShiftedPartition.representative a.val r.val) a.val))*
              ShortDraftTrace.breveE (ninthCuspFrequency h*
                eisEmbedding (a.val+3*GaussianShiftedPartition.representative a.val r.val)/eisEmbedding ((u:Eis)*a.val))) := by
    rw [←(unitCuspIndexEquiv u).tsum_eq]
    exact (unitLowerIntegral_sum_translate h a.val k
      (GaussianShiftedPartition.representative a.val r.val) u j (primaryLower_ne_zero a)
      (primaryLower_primary a) hu hk v hv s (by linarith)).trans
        (unitLowerTerm_fourier_integral u v hv s (ninthCuspFrequency h) a.val _ (primaryLower_ne_zero a))
  simp_rw [hinner]
  exact tsum_mul_left
end OAI.CubicEisenstein
