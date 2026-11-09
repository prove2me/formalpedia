-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.maskedPairDualTail_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T03:56:03.684299+00:00
-- url     : https://prove2.me/submissions/11670ebf-8b43-43fc-8df2-07c251352164

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CommonMasks
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_QuotientTopology
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ScaleCaps
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_dualSquarefreeTail_bound
import Theorems.Thm_OAI_CanonicalQuadraticSieve_dual_truncation_prefactor_bound
import Theorems.Thm_OAI_CanonicalQuadraticSieve_quadraticRow_norm_le_one
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_norm_ideal_moebius_le_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_apply
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_zero
import Theorems.Thm_OAI_QuadraticInitialBound_norm_ideal_moebius_le_one
import Theorems.Thm_OAI_QuadraticInitialBound_quadraticRow_norm_le_one
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
attribute [local simp] OAI.CubicEisenstein.spatialTriple_one
attribute [local simp] OAI.CubicEisenstein.spatialTriple_two
attribute [local simp] OAI.CubicEisenstein.spatialTriple_zero
attribute [local simp] OAI.CubicReflectionKernel.logSchwartz_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.FirstPassCubeLabels.coreRayTwist_prod
attribute [local simp] OAI.FirstPassCubeLabels.twisted_core_product
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_norm
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_twice
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_apply
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_zero
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newLabel
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newRow
attribute [local simp] OAI.SecondPassIntegration.conjugateProfile_apply



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
open scoped BigOperators Classical SchwartzMap
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ (G I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (M N K : ℝ),
      G≠0 → I≠0 → J≠0 → 0<M → 1≤N → 0≤K →
      N/2≤(Ideal.absNorm I:ℝ) → (Ideal.absNorm I:ℝ)≤N →
      N/2≤(Ideal.absNorm J:ℝ) → (Ideal.absNorm J:ℝ)≤N →
      ‖maskedPairDualTail G I J W M K‖ ≤
        (2*M/N)*(idealDivisors G).card*
          ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
            ((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*
              (1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A)) := by
  obtain ⟨s,C,hC,hbound⟩ := dualSquarefreeTail_bound A
  refine ⟨s,C,hC,?_⟩
  intro G I J W M N K hG hI hJ hM hN hK hIl hIu hJl hJu
  have hNG : 0<(Ideal.absNorm G:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hG (Ideal.absNorm_eq_zero_iff.mp hz))
  have hNI : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hNJ : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hN0 : 0<N := by linarith
  let t0 := M/((Ideal.absNorm G:ℝ)*N*N)
  let T := (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 t0)^2*(1+t0*K)^A)
  have ht0 : 0<t0 := by dsimp only [t0]; positivity
  have hT : 0≤T := by dsimp only [T]; positivity
  have hterm (q : Ideal O) (hq : q∈idealDivisors G) :
      ‖((UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ))*
        dualSquarefreeTail I J W
          (M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))) K‖ ≤ T := by
    have hqG := (mem_idealDivisors hG).mp hq
    have hq0 : q≠0 := by intro hz; rw [hz,zero_dvd_iff] at hqG; exact hG hqG
    have hq1 : 1≤(Ideal.absNorm q:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hq0 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hqN : (Ideal.absNorm q:ℝ)≤(Ideal.absNorm G:ℝ) := by
      exact_mod_cast Nat.le_of_dvd (by exact_mod_cast hNG) (map_dvd Ideal.absNorm hqG)
    have ht : 0<M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by positivity
    have htlo : t0≤M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
      apply div_le_div_of_nonneg_left hM.le (by positivity)
      gcongr
    have hc : ‖(UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ)‖≤1 := by
      rw [norm_div,norm_mul,Complex.norm_natCast]
      have hp : ‖unrestrictedPairCharacter I J q‖≤1 := by
        rw [unrestrictedPairCharacter,norm_mul]
        exact (mul_le_mul (quadraticRow_norm_le_one _ _) (quadraticRow_norm_le_one _ _)
          (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      calc
        _ ≤ (1*1)/(Ideal.absNorm q:ℝ) := by
          gcongr
          exact QuadraticInitialBound.norm_ideal_moebius_le_one q
        _ ≤ 1 := by simpa only [one_mul,div_one] using (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hq1)
    have hb : ‖dualSquarefreeTail I J W
        (M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))) K‖≤T := by
      apply (hbound I J W _ K ht hK).trans
      dsimp only [T]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      gcongr
    rw [norm_mul]
    exact (mul_le_mul hc hb (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hpref : ‖(M:ℂ)/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)):ℂ)‖≤2*M/N := by
    simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hM.le,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [mul_one,one_mul] using
      dual_truncation_prefactor_bound M 1 N (Ideal.absNorm I) (Ideal.absNorm J)
        hM (by norm_num) hN0 ⟨hIl,hIu⟩ ⟨hJl,hJu⟩
  rw [maskedPairDualTail,norm_mul]
  calc
    _ ≤ (2*M/N)*(∑ q ∈ idealDivisors G, T) := mul_le_mul hpref
      ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm)) (norm_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,T,t0]; ring
end OAI.CanonicalQuadraticSieve
