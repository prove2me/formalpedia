-- Prove2me | solution 1 for OAI.SecondPassArithmetic.postCommonSmoothPair_fixed_tests
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:33:22.604213+00:00
-- url     : https://prove2.me/submissions/a9b27f29-34a3-445d-8918-731ae095f0b7

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_SecondPoisson
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_PrincipalTruncation
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_FrequencyTwists
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_finite_triple_phase_integral
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
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
import Theorems.Thm_OAI_JointLogSeparation_seven_phase_factor
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
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
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply


attribute [local simp] OAI.JointLogSeparation.frequencyTwist_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_twice
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_norm

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
open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog firstLogDensity)
open JointLogSeparation (outerWindow fixedColumnTest)
open FourierBridge (logPhase)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ)
    (z ud ue uv kap X₁ X₂ R : ℝ) (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ a a' : ℝ,
      outerWindow V z ud ue uv kap * V 5 a * V 6 a' * A₁ (z+a) * A₂ (z+a') *
        EisensteinSchwartzPoisson.paperRadialFourier W (R * Real.exp (kap-ud-2*ue-2*uv-a-a')) =
      ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        outerWindow V z ud ue uv kap * logPhase (t₁+t₂) z *
          logPhase t₃ (kap-ud-2*ue-2*uv) *
          fixedColumnTest (V 5) (t₁-t₃) a * fixedColumnTest (V 6) (t₂-t₃) a' *
          ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) :
    postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m f y₁ y₂ A₁ A₂ W V z ud ue uv kap X₁ X₂ R =
    ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      (outerWindow V z ud ue uv kap * logPhase (t₁+t₂) z *
        logPhase t₃ (kap-ud-2*ue-2*uv) * ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) *
      star (fixedChildRow p hp hcop hg F Ψ₁ m
        (fixedSecondTest p (V 5) X₁ t₁ t₃ true) f y₁) *
      fixedChildRow p hp hcop hg F Ψ₂ m
        (fixedSecondTest p (V 6) X₂ t₂ t₃ false) f y₂ := by
  let B₁ := fun N => secondChildColumn p hp hcop hg Ψ₁ m f y₁ (fun _ => 1) N
  let B₂ := fun M => secondChildColumn p hp hcop hg Ψ₂ m f y₂ (fun _ => 1) M
  let q := fun (i : Finset ι × Finset ι) =>
    outerWindow V z ud ue uv kap * V 5 (columnLog p X₁ i.1) * V 6 (columnLog p X₂ i.2) *
      star (B₁ i.1) * B₂ i.2
  let K := fun (i : Finset ι × Finset ι) (t₁ t₂ t₃ : ℝ) =>
    (logPhase t₁ (z + columnLog p X₁ i.1) * (𝓕 A₁) t₁) *
      ((logPhase t₂ (z + columnLog p X₂ i.2) * (𝓕 A₂) t₂) *
        ((logPhase t₃ (kap-ud-2*ue-2*uv-columnLog p X₁ i.1-columnLog p X₂ i.2) * b t₃) * q i))
  have hterm (N M : Finset ι) : star (B₁ N) * B₂ M *
      (outerWindow V z ud ue uv kap * V 5 (columnLog p X₁ N) * V 6 (columnLog p X₂ M) *
        A₁ (z+columnLog p X₁ N) * A₂ (z+columnLog p X₂ M) *
        EisensteinSchwartzPoisson.paperRadialFourier W
          (R * Real.exp (kap-ud-2*ue-2*uv-columnLog p X₁ N-columnLog p X₂ M))) =
      ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, K (N,M) t₁ t₂ t₃ := by
    rw [hsep]
    simp_rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t₁
    apply integral_congr_ae
    filter_upwards [] with t₂
    apply integral_congr_ae
    filter_upwards [] with t₃
    have hphase := JointLogSeparation.seven_phase_factor z ud ue uv kap
      (columnLog p X₁ N) (columnLog p X₂ M) t₁ t₂ t₃
    dsimp only [K, q]
    unfold fixedColumnTest
    calc
      _ = (outerWindow V z ud ue uv kap * V 5 (columnLog p X₁ N) * V 6 (columnLog p X₂ M) *
        star (B₁ N) * B₂ M) *
        (logPhase (t₁+t₂) z * logPhase t₃ (kap-ud-2*ue-2*uv) *
          logPhase (t₁-t₃) (columnLog p X₁ N) * logPhase (t₂-t₃) (columnLog p X₂ M)) *
        ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃) := by ring
      _ = _ := by rw [← hphase]; ring
  calc
    _ = ∑ i ∈ F.powerset ×ˢ F.powerset, ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, K i t₁ t₂ t₃ := by
      simp only [postCommonSmoothPair, Finset.sum_product]
      exact Finset.sum_congr rfl (fun N _ => Finset.sum_congr rfl (fun M _ => hterm N M))
    _ = ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∑ i ∈ F.powerset ×ˢ F.powerset, K i t₁ t₂ t₃ :=
      JointLogSeparation.finite_triple_phase_integral _ (𝓕 A₁) (𝓕 A₂) b _ _ _ q
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t₁
      apply integral_congr_ae
      filter_upwards [] with t₂
      apply integral_congr_ae
      filter_upwards [] with t₃
      simp only [Finset.sum_product]
      have hcols : (∑ N ∈ F.powerset, ∑ M ∈ F.powerset, K (N,M) t₁ t₂ t₃) =
          (outerWindow V z ud ue uv kap * logPhase (t₁+t₂) z *
            logPhase t₃ (kap-ud-2*ue-2*uv) * ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) *
          (∑ N ∈ F.powerset, star (B₁ N) * fixedColumnTest (V 5) (t₁-t₃) (columnLog p X₁ N)) *
          (∑ M ∈ F.powerset, B₂ M * fixedColumnTest (V 6) (t₂-t₃) (columnLog p X₂ M)) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        conv_rhs => rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro N hN
        apply Finset.sum_congr rfl
        intro M hM
        have hphase := JointLogSeparation.seven_phase_factor z ud ue uv kap
          (columnLog p X₁ N) (columnLog p X₂ M) t₁ t₂ t₃
        dsimp only [K, q]
        unfold fixedColumnTest
        calc
          _ = (outerWindow V z ud ue uv kap * V 5 (columnLog p X₁ N) * V 6 (columnLog p X₂ M) *
            star (B₁ N) * B₂ M) *
            (logPhase t₁ (z+columnLog p X₁ N) * logPhase t₂ (z+columnLog p X₂ M) *
              logPhase t₃ (kap-ud-2*ue-2*uv-columnLog p X₁ N-columnLog p X₂ M)) *
            ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃) := by ring
          _ = _ := by rw [hphase]; ring
      rw [hcols]
      have hleft : (∑ N ∈ F.powerset, star (B₁ N) *
          fixedColumnTest (V 5) (t₁-t₃) (columnLog p X₁ N)) =
          star (fixedChildRow p hp hcop hg F Ψ₁ m
            (fixedSecondTest p (V 5) X₁ t₁ t₃ true) f y₁) := by
        simp only [fixedChildRow, star_sum]
        apply Finset.sum_congr rfl
        intro N hN
        simp only [secondChildColumn, fixedSecondTest, ite_true, B₁,
          star_mul, star_star, mul_one]
        ring
      have hright : (∑ N ∈ F.powerset, B₂ N *
          fixedColumnTest (V 6) (t₂-t₃) (columnLog p X₂ N)) =
          fixedChildRow p hp hcop hg F Ψ₂ m
            (fixedSecondTest p (V 6) X₂ t₂ t₃ false) f y₂ := by
        apply Finset.sum_congr rfl
        intro N hN
        simp only [secondChildColumn, fixedSecondTest, Bool.false_eq_true, ite_false, B₂, mul_one]
      rw [hleft, hright]
end OAI.SecondPassArithmetic
