-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.lattice_profile_nonzero_scaled_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:22:36.972337+00:00
-- url     : https://prove2.me/submissions/d77fac46-49f4-42a6-b363-019d51a991be

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ActiveConductor
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_MixedConversion
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_scaled_eisenstein_cauchy_summable
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_scaled_eisenstein_cauchy_small
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_one_le_eisenstein_norm_sq
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_cauchy_large_scale_pointwise
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_eisensteinCauchyMass_nonneg
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_eisensteinCauchyMass_subtype
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_eisenstein_cauchy_summable
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply



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
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open OAI.EisensteinSchwartzPoisson
open ConcreteTraceCRT ActualEisensteinCubic
namespace OAI.EisensteinSchwartzPoisson
theorem _root_.solution
    (F : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ t : ℝ, 0 ≤ t → (1 + t) ^ 2 * ‖F t‖ ≤ B)
    (K : ℝ) (hK : 0 < K) :
    K * (∑' h : {h : O // h ≠ 0}, ‖F (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
      (4 * (1 + Real.pi) ^ 2 + 4 * eisensteinCauchyMass) * B := by
  have hm (h : O) : ‖F (K * ‖eisEmbedding h‖ ^ 2)‖ ≤
      B * ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using hF (K * ‖eisEmbedding h‖ ^ 2) (by positivity)
  have hs := scaled_eisenstein_cauchy_summable K hK
  have hf : Summable (fun h : O => ‖F (K * ‖eisEmbedding h‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hm (hs.mul_left B)
  have hsub := hf.subtype (fun h : O => h ≠ 0)
  have hc := eisenstein_cauchy_summable.subtype (fun h : O => h ≠ 0)
  by_cases hK1 : K ≤ 1
  · have htotal : (∑' h : {h : O // h ≠ 0}, ‖F (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
        ∑' h : O, ‖F (K * ‖eisEmbedding h‖ ^ 2)‖ :=
      hsub.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
        (fun _ _ => norm_nonneg _) (fun _ => le_rfl) hf
    have hbound := hf.tsum_le_tsum hm (hs.mul_left B)
    rw [tsum_mul_left] at hbound
    calc
      _ ≤ K * (B * ∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (htotal.trans hbound) hK.le
      _ = B * (K * ∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) := by ring
      _ ≤ B * (4 * (1 + Real.pi) ^ 2) :=
        mul_le_mul_of_nonneg_left (scaled_eisenstein_cauchy_small K hK hK1) hB
      _ ≤ _ := by nlinarith [eisensteinCauchyMass_nonneg]
  · have hp (h : {h : O // h ≠ 0}) :
        K * ‖F (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
          (4 * B) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := by
      calc
        _ ≤ K * (B * ((1 + K * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (hm h.val) hK.le
        _ = B * (K * ((1 + K * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) := by ring
        _ ≤ B * (4 * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (cauchy_large_scale_pointwise K _
            (le_of_not_ge hK1) (one_le_eisenstein_norm_sq h.val h.property)) hB
        _ = _ := by ring
    calc
      _ = ∑' h : {h : O // h ≠ 0}, K * ‖F (K * ‖eisEmbedding h.val‖ ^ 2)‖ := tsum_mul_left.symm
      _ ≤ ∑' h : {h : O // h ≠ 0}, (4 * B) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ :=
        (hsub.mul_left K).tsum_le_tsum hp (hc.mul_left (4 * B))
      _ = (4 * B) * ∑' h : {h : O // h ≠ 0}, ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := tsum_mul_left
      _ ≤ (4 * B) * eisensteinCauchyMass := mul_le_mul_of_nonneg_left
        (eisensteinCauchyMass_subtype (fun h : O => h ≠ 0)) (by positivity)
      _ ≤ _ := by nlinarith [sq_nonneg (1 + Real.pi)]
end OAI.EisensteinSchwartzPoisson
