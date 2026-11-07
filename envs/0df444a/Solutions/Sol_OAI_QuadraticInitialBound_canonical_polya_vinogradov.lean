-- Prove2me | solution 1 for OAI.QuadraticInitialBound.canonical_polya_vinogradov
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:33:11.552846+00:00
-- url     : https://prove2.me/submissions/6a5b2b5d-ccc3-4575-91ae-ee495ca13391

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RayCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoefficientCancellation
import Theorems.Thm_OAI_QuadraticInitialBound_pv_lattice_bound
import Theorems.Thm_OAI_QuadraticInitialBound_finiteSexticRow_norm_le_one
import Theorems.Thm_OAI_ActualEisensteinCubic_canonical_radial_poisson_normalized
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSexticRow_zero
import Theorems.Thm_OAI_ActualEisensteinCubic_norm_canonicalNormalizedGauss
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRadialFourier_lattice_summable_norm
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk



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
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap
open OAI.QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
namespace OAI.QuadraticInitialBound
theorem _root_.solution {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, lambda ∉ P i) (hc : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, finiteSexticRow P hg j z * W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      pvControl W * ‖eisEmbedding (finitePrimeModulus P)‖ := by
  let c := finitePrimeModulus P
  let q := ‖eisEmbedding c‖
  have hq : 0 < q := norm_pos_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P))
  let t := M / q ^ 2
  have ht : 0 < t := div_pos hM (sq_pos_of_pos hq)
  let F : O → ℂ := fun h => star (finiteSexticRow P hg j h) *
    paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)
  have hF (h : O) : ‖F h‖ ≤ ‖paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)‖ := by
    dsimp only [F]
    rw [norm_mul, norm_star]
    exact mul_le_of_le_one_left (norm_nonneg _) (finiteSexticRow_norm_le_one P hg j h)
  have hs := paperRadialFourier_lattice_summable_norm W t ht
  have hFs : Summable (fun h : O => ‖F h‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF hs
  have hzero : F 0 = 0 := by simp only [F, finiteSexticRow_zero, star_zero, zero_mul]
  have heq : (∑' h : O, F h) = ∑' h : {h : O // h ≠ 0}, F h := by
    symm
    apply tsum_subtype_eq_of_support_subset
    intro h hh
      hz
    subst h
    exact hh hzero
  have hn : ‖∑' h : O, F h‖ ≤
      ∑' h : {h : O // h ≠ 0}, ‖paperRadialFourier W (t * ‖eisEmbedding h.val‖ ^ 2)‖ := by
    rw [heq]
    exact (norm_tsum_le_tsum_norm (hFs.subtype _)).trans
      ((hFs.subtype _).tsum_le_tsum (fun h => hF h) (hs.subtype _))
  have hbound : t * ‖∑' h : O, F h‖ ≤ pvControl W :=
    (mul_le_mul_of_nonneg_left hn ht.le).trans (pv_lattice_bound W t ht)
  rw [canonical_radial_poisson_normalized P hcop hg hc j hj0 hj6 W M hM]
  have hargs (h : O) : M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2 =
      t * ‖eisEmbedding h‖ ^ 2 := by dsimp [t, q]; ring
  change ‖((M : ℂ) * canonicalNormalizedGauss P hcop hg j / (q : ℂ)) *
    ∑' h : O, star (finiteSexticRow P hg j h) *
      paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)‖ ≤ _
  simp_rw [hargs]
  change ‖((M : ℂ) * canonicalNormalizedGauss P hcop hg j / (q : ℂ)) * ∑' h : O, F h‖ ≤ _
  rw [norm_mul, norm_div, norm_mul, norm_canonicalNormalizedGauss P hcop hg hc j hj0 hj6,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  change M / q * ‖∑' h : O, F h‖ ≤ pvControl W * q
  calc
    _ = q * (t * ‖∑' h : O, F h‖) := by dsimp [t]; field_simp
    _ ≤ q * pvControl W := mul_le_mul_of_nonneg_left hbound hq.le
    _ = _ := mul_comm _ _
end OAI.QuadraticInitialBound
