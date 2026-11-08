-- Prove2me | solution 1 for OAI.CubicEisenstein.denominator_integral_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:59:09.85985+00:00
-- url     : https://prove2.me/submissions/34f4ca2d-193f-46ff-a6bb-ccf75175f3d7

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_HyperbolicSpace
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RowMajorants
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FourierCoefficients
import Theorems.Thm_OAI_CubicEisenstein_hasSum_primitiveRowIntegrals
import Theorems.Thm_OAI_CubicEisenstein_primitiveRowIntegral_sum_translate
import Theorems.Thm_OAI_CubicEisenstein_primitiveTerm_fourier_integral
import Theorems.Thm_OAI_CubicEisenstein_denominator_sum_residues


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
open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
namespace OAI.CubicEisenstein
theorem _root_.solution (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re)
    (h : O) (c : LevelLower) (hc : c.1 ≠ 0) :
    (∑' d : AdmissibleDenominator c.1,primitiveRowIntegral v s (cuspFrequency h) c.1 d.1)=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*
        ((‖eisEmbedding c.1‖^2:ℝ):ℂ)^(-s)*arithmeticResidueSum h c.1 := by
  have hsum : Summable (fun d : AdmissibleDenominator c.1 =>
      primitiveRowIntegral v s (cuspFrequency h) c.1 d.1) :=
    (hasSum_primitiveRowIntegrals v hv s (cuspFrequency h) hs).summable.sigma_factor c
  rw [denominator_sum_residues c.1 hc
    (fun d : O => primitiveRowIntegral v s (cuspFrequency h) c.1 d) hsum]
  calc
    _ = ∑' r : AdmissibleResidue c.1, ∫ z : ℂ,
        primitiveTerm z v s c.1 (denominatorRep c.1 r.1)*
          ShortDraftTrace.breveE (-cuspFrequency h*z) := by
      apply tsum_congr
      intro r
      exact primitiveRowIntegral_sum_translate v hv s (by linarith) h c.1
        (denominatorRep c.1 r.1) hc c.2 r.2.2
    _ = _ := by
      simp_rw [primitiveTerm_fourier_integral v hv s (cuspFrequency h) c.1 _ hc]
      exact tsum_mul_left
end OAI.CubicEisenstein
