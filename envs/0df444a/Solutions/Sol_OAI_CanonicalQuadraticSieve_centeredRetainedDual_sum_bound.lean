-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.centeredRetainedDual_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T22:31:34.203803+00:00
-- url     : https://prove2.me/submissions/bfe87eb9-f6b5-4719-b020-016aa69bdfa9

import Mathlib
import Definitions.Def_OAIHecke78B007

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SecondPoissonScale
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace ActualEisensteinCubic

private theorem mask_powerset {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (p : ι → Prop) [DecidablePred p] :
    (if ∃ i ∈ S, p i then (0 : ℂ) else 1) =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card *
        if ∀ i ∈ E, p i then 1 else 0 := by
  have hprod : (if ∃ i ∈ S, p i then (0 : ℂ) else 1) =
      ∏ i ∈ S, (1 - if p i then (1 : ℂ) else 0) := by
    by_cases h : ∃ i ∈ S, p i
    · rw [if_pos h]
      obtain ⟨i, hi, hp⟩ := h
      symm
      apply Finset.prod_eq_zero hi
      simp [hp]
    · rw [if_neg h]
      symm
      apply Finset.prod_eq_one
      intro i hi
      simp [show ¬p i from fun hp => h ⟨i, hi, hp⟩]
  rw [hprod, Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro E hE
  simp only [Finset.prod_const_one, mul_one]
  congr 1
  by_cases h : ∀ i ∈ E, p i
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [h i hi]
  · rw [if_neg h]
    push Not at h
    obtain ⟨i, hi, hp⟩ := h
    apply Finset.prod_eq_zero hi
    simp [hp]

theorem rowCoprimeMask_subsets
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι) (u : O) :
    rowCoprimeMask P S u =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card *
        if ∀ i ∈ E, u ∈ P i then 1 else 0 := by
  classical
  exact mask_powerset S (fun i => u ∈ P i)

theorem prime_product_moebius
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hprime : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (S : Finset ι) :
    (UniqueFactorizationMonoid.moebius (∏ i ∈ S, P i) : ℂ) =
      (-1 : ℂ) ^ S.card := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, UniqueFactorizationMonoid.moebius_one, Int.cast_one, Finset.card_empty, pow_zero]
  | @insert i S hi ih =>
    have hcop : IsCoprime (P i) (∏ j ∈ S, P j) := by
      apply IsCoprime.prod_right
      intro j hj
      apply Ideal.isCoprime_of_isMaximal
      exact hinj.ne (by intro h; subst j; exact hi hj)
    rw [Finset.prod_insert hi, hcop.isRelPrime.moebius_mul,
      (hprime i).irreducible.moebius_eq, Int.cast_mul, Int.cast_neg,
      Int.cast_one, ih, Finset.card_insert_of_notMem hi, pow_succ]
    ring

theorem mem_prime_product_iff
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (u : O) :
    u ∈ (∏ i ∈ S, P i) ↔ ∀ i ∈ S, u ∈ P i := by
  rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime]
  · simp
  · intro i hi j hj hij
    exact Ideal.isCoprime_of_isMaximal (hinj.ne hij)

end ActualEisensteinCubic

namespace EisensteinSchwartzPoisson
open MeasureTheory Filter LineDeriv
open scoped FourierTransform SchwartzMap Real RealInnerProductSpace

theorem fourier_prod_eq_iterated (f : LogPlane → ℂ) (hf : Integrable f) (ξ η : ℝ) :
    𝓕 f (WithLp.toLp 2 (ξ, η)) =
      𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => f (WithLp.toLp 2 (x, y))) η) ξ := by
  let w : LogPlane := WithLp.toLp 2 (ξ, η)
  let G : LogPlane → ℂ := fun z => Real.fourierChar (-⟪z, w⟫) • f z
  have hG : Integrable G := (Real.fourierIntegral_convergent_iff w).mpr hf
  have hGp : Integrable (fun z : ℝ × ℝ => G (WithLp.toLp 2 z)) :=
    (WithLp.volume_preserving_toLp ℝ ℝ).integrable_comp_of_integrable hG
  calc
    𝓕 f (WithLp.toLp 2 (ξ, η)) = ∫ z : LogPlane, G z := rfl
    _ = ∫ z : ℝ × ℝ, G (WithLp.toLp 2 z) :=
      ((WithLp.volume_preserving_toLp ℝ ℝ).integral_comp
        (MeasurableEquiv.toLp 2 (ℝ × ℝ)).measurableEmbedding G).symm
    _ = ∫ x : ℝ, ∫ y : ℝ, G (WithLp.toLp 2 (x, y)) := integral_prod _ hGp
    _ = 𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => f (WithLp.toLp 2 (x, y))) η) ξ := by
      simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          simp only [G, w, WithLp.prod_inner_apply,
            neg_add, Real.fourierChar.map_add_eq_mul, Circle.smul_def, smul_eq_mul,
            Circle.coe_mul, mul_assoc]

theorem verticalMajorant_integrable (f : SchwartzMap ℂ ℂ) : Integrable (verticalMajorant f) :=
  integrable_inv_one_add_sq.const_mul _

theorem norm_le_verticalMajorant (f : SchwartzMap ℂ ℂ) (x y : ℝ) :
    ‖f (complexPoint x y)‖ ≤ verticalMajorant f y := by
  have h0 := SchwartzMap.norm_le_seminorm ℝ f (complexPoint x y)
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ f 2 (complexPoint x y)
  have hy : y ^ 2 ≤ ‖complexPoint x y‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, complexPoint]
    nlinarith [sq_nonneg x]
  have hym := mul_le_mul_of_nonneg_right hy (norm_nonneg (f (complexPoint x y)))
  have hden : 0 < 1 + y ^ 2 := by positivity
  rw [verticalMajorant, ← div_eq_mul_inv]
  apply (le_div_iff₀ hden).mpr
  nlinarith

theorem partialFourier_continuous (f : SchwartzMap ℂ ℂ) (η : ℝ) :
    Continuous (partialFourier f η) := by
  change Continuous (fun x : ℝ => ∫ y : ℝ,
    Real.fourierChar (-inner ℝ y η) • f (complexPoint x y))
  apply continuous_of_dominated
    (bound := verticalMajorant f)
  · intro x
    have hline : Continuous (fun y : ℝ => complexPoint x y) :=
      Complex.equivRealProdCLM.symm.continuous.comp (continuous_const.prodMk continuous_id)
    exact ((by fun_prop : Continuous (fun y : ℝ => Real.fourierChar (-inner ℝ y η))).smul
      (f.continuous.comp hline)).aestronglyMeasurable
  · intro x
    exact Eventually.of_forall fun y => by
      simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul] using
        norm_le_verticalMajorant f x y
  · exact verticalMajorant_integrable f
  · exact Eventually.of_forall fun y => by
      have hf : Continuous (fun x : ℝ => f (complexPoint x y)) :=
        f.continuous.comp (horizontal_isometry y).continuous
      exact continuous_const.smul hf

theorem partialFourier_integrable (f : SchwartzMap ℂ ℂ) (η : ℝ) :
    Integrable (partialFourier f η) := by
  let G : ℂ → ℂ := fun z => Real.fourierChar (-inner ℝ z.im η) • f z
  have hG : Integrable G := f.integrable.norm.mono'
    (by fun_prop : Continuous G).aestronglyMeasurable
    (Eventually.of_forall fun z => by
      simp only [G, Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
      exact le_rfl)
  have hGp : Integrable (fun z : ℝ × ℝ => G (Complex.measurableEquivRealProd.symm z)) :=
    Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_of_integrable hG
  change Integrable (fun x : ℝ => ∫ y : ℝ,
    Real.fourierChar (-inner ℝ y η) • f (complexPoint x y))
  simpa only [G, Complex.measurableEquivRealProd_symm_apply, complexPoint]
    using hGp.integral_prod_left

theorem fourier_partialFourier (f : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    𝓕 (partialFourier f η) ξ = 𝓕 (f : ℂ → ℂ) (complexPoint ξ η) := by
  let fp : SchwartzMap LogPlane ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ planeComplexIso.toContinuousLinearEquiv f
  have hprod := fourier_prod_eq_iterated (fp : LogPlane → ℂ) fp.integrable ξ η
  have hcoe : (fp : LogPlane → ℂ) = (f : ℂ → ℂ) ∘ planeComplexIso := rfl
  rw [hcoe, Real.fourier_comp_linearIsometry] at hprod
  change 𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => f (complexPoint x y)) η) ξ = _
  simpa only [Function.comp_apply, planeComplexIso_apply] using hprod.symm

theorem partialFourierSchwartz_apply (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    partialFourierSchwartz f η x = partialFourier f η x := by
  have heq : 𝓕 (partialFourier f η) =
      (horizontalSlice (𝓕 f) η : ℝ → ℂ) := by
    funext ξ
    rw [fourier_partialFourier, horizontalSlice_apply]
    exact (congrFun (SchwartzMap.fourier_coe f) (complexPoint ξ η)).symm
  have hi : Integrable (𝓕 (partialFourier f η)) := by
    rw [heq]
    exact (horizontalSlice (𝓕 f) η).integrable
  change (𝓕⁻ (horizontalSlice (𝓕 f) η)) x = _
  rw [congrFun (SchwartzMap.fourierInv_coe (horizontalSlice (𝓕 f) η)) x, ← heq]
  exact (partialFourier_integrable f η).fourierInv_fourier_eq hi
    (partialFourier_continuous f η).continuousAt

theorem partialFourierSchwartz_coe (f : SchwartzMap ℂ ℂ) (η : ℝ) :
    (partialFourierSchwartz f η : ℝ → ℂ) = partialFourier f η :=
  funext (partialFourierSchwartz_apply f η)

theorem horizontal_hasFDerivAt (η x : ℝ) :
    HasFDerivAt (fun y : ℝ => complexPoint y η) Complex.ofRealCLM x := by
  have heq : (fun y : ℝ => complexPoint y η) =
      (fun y : ℝ => Complex.ofRealCLM y + Complex.I * (η : ℂ)) := by
    funext y
    exact complexPoint_eq y η
  rw [heq]
  exact Complex.ofRealCLM.hasFDerivAt.add_const _

theorem horizontalSlice_lineDerivOp (F : SchwartzMap ℂ ℂ) (η : ℝ) :
    ∂_{(1 : ℝ)} (horizontalSlice F η) = horizontalSlice (∂_{(1 : ℂ)} F) η := by
  apply SchwartzMap.ext
  intro x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, horizontalSlice_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hcomp := (F.hasFDerivAt (complexPoint x η)).comp x (horizontal_hasFDerivAt η x)
  change fderiv ℝ (fun y : ℝ => F (complexPoint y η)) x (1 : ℝ) = _
  change fderiv ℝ ((F : ℂ → ℂ) ∘ (fun y => complexPoint y η)) x (1 : ℝ) = _
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.ofReal_one]

theorem horizontalSlice_lineDerivOp_twice (F : SchwartzMap ℂ ℂ) (η : ℝ) :
    ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (horizontalSlice F η)) =
      horizontalSlice (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F)) η := by
  rw [horizontalSlice_lineDerivOp, horizontalSlice_lineDerivOp]

theorem summable_norm_of_cauchy_product (F : ℤ × ℤ → ℂ) (C : ℝ)
    (hF : ∀ p, ‖F p‖ ≤ C *
      ((1 + (p.1 : ℝ) ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2)⁻¹)) :
    Summable (fun p => ‖F p‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF
    (summable_int_cauchy_product.mul_left C)

theorem plane_schwartz_product_decay (F : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F (complexPoint ξ η)‖ ≤
      planeDecayConstant F := by
  let z := complexPoint ξ η
  have hz : ‖z‖ ^ 2 = ξ ^ 2 + η ^ 2 := by
    rw [Complex.sq_norm]
    simp [z, Complex.normSq_apply, complexPoint, sq]
  have h0 := SchwartzMap.norm_le_seminorm ℝ F z
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 2 z
  have h4 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 4 z
  have hz4 : ‖z‖ ^ 4 = (ξ ^ 2 + η ^ 2) ^ 2 := by
    calc
      ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 := by ring
      _ = (ξ ^ 2 + η ^ 2) ^ 2 := congrArg (fun t : ℝ => t ^ 2) hz
  have hxy : ξ ^ 2 * η ^ 2 ≤ ‖z‖ ^ 4 := by
    rw [hz4]
    nlinarith [sq_nonneg (ξ ^ 2), sq_nonneg (η ^ 2),
      mul_nonneg (sq_nonneg ξ) (sq_nonneg η)]
  have hm := mul_le_mul_of_nonneg_right hxy (norm_nonneg (F z))
  rw [hz] at h2
  change ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F z‖ ≤ _
  unfold planeDecayConstant
  nlinarith

theorem norm_horizontalSlice_le (F : SchwartzMap ℂ ℂ) (η ξ : ℝ) :
    ‖horizontalSlice F η ξ‖ ≤
      (planeDecayConstant F / (1 + η ^ 2)) * (1 + ξ ^ 2)⁻¹ := by
  rw [horizontalSlice_apply, ← div_eq_mul_inv, div_div]
  apply (le_div_iff₀ (by positivity : 0 < (1 + η ^ 2) * (1 + ξ ^ 2))).mpr
  nlinarith [plane_schwartz_product_decay F ξ η]

theorem norm_inverse_horizontalSlice_le (F : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ‖(𝓕⁻ (horizontalSlice F η)) x‖ ≤
      (planeDecayConstant F / (1 + η ^ 2)) * Real.pi := by
  rw [congrFun (SchwartzMap.fourierInv_coe (horizontalSlice F η)) x,
    Real.fourierInv_eq]
  have hb : Integrable (fun ξ : ℝ =>
      (planeDecayConstant F / (1 + η ^ 2)) * (1 + ξ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have h := norm_integral_le_of_norm_le
    (f := fun ξ : ℝ => Real.fourierChar (inner ℝ ξ x) • horizontalSlice F η ξ) hb (Eventually.of_forall fun ξ => by
    simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul] using
      norm_horizontalSlice_le F η ξ)
  simpa only [integral_const_mul, integral_univ_inv_one_add_sq] using h

theorem norm_inverse_lineDeriv (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖(𝓕⁻ (∂_{(1 : ℝ)} g)) x‖ =
      (2 * Real.pi) * |x| * ‖(𝓕⁻ g) x‖ := by
  have ht : (fun u : ℝ => inner ℝ u (1 : ℝ)).HasTemperateGrowth := by fun_prop
  have hc : ‖(-(2 * Real.pi * Complex.I) : ℂ)‖ = 2 * Real.pi := by
    simp [ Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [SchwartzMap.fourierInv_lineDerivOp_eq]
  simp only [_root_.smul_apply, SchwartzMap.smulLeftCLM_apply_apply ht,
    norm_smul, hc]
  simp [RCLike.inner_apply, Real.norm_eq_abs, mul_assoc]

theorem sq_mul_norm_inverse_le_second (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    x ^ 2 * ‖(𝓕⁻ g) x‖ ≤ ‖(𝓕⁻ (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} g))) x‖ := by
  rw [norm_inverse_lineDeriv, norm_inverse_lineDeriv]
  have hp : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  calc
    x ^ 2 * ‖(𝓕⁻ g) x‖ ≤ ((2 * Real.pi) ^ 2 * x ^ 2) * ‖(𝓕⁻ g) x‖ :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (sq_nonneg x) hp) (norm_nonneg _)
    _ = ((2 * Real.pi) ^ 2 * |x| ^ 2) * ‖(𝓕⁻ g) x‖ := by rw [sq_abs]
    _ = _ := by ring

theorem inverse_horizontalSlice_product_decay (F : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ((1 + x ^ 2) * (1 + η ^ 2)) * ‖(𝓕⁻ (horizontalSlice F η)) x‖ ≤
      Real.pi * (planeDecayConstant F +
        planeDecayConstant (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F))) := by
  have h0 := norm_inverse_horizontalSlice_le F η x
  have h2a := sq_mul_norm_inverse_le_second (horizontalSlice F η) x
  rw [horizontalSlice_lineDerivOp_twice] at h2a
  have h2 := h2a.trans
    (norm_inverse_horizontalSlice_le (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F)) η x)
  have hden : 0 < 1 + η ^ 2 := by positivity
  have h0' : ‖(𝓕⁻ (horizontalSlice F η)) x‖ * (1 + η ^ 2) ≤
      planeDecayConstant F * Real.pi := by
    apply (le_div_iff₀ hden).mp
    simpa only [div_mul_eq_mul_div] using h0
  have h2' : (x ^ 2 * ‖(𝓕⁻ (horizontalSlice F η)) x‖) * (1 + η ^ 2) ≤
      planeDecayConstant (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F)) * Real.pi := by
    apply (le_div_iff₀ hden).mp
    simpa only [div_mul_eq_mul_div] using h2
  nlinarith

theorem partialFourier_product_decay (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ((1 + x ^ 2) * (1 + η ^ 2)) * ‖partialFourier f η x‖ ≤
      partialFourierDecayConstant f := by
  rw [← partialFourierSchwartz_apply]
  exact inverse_horizontalSlice_product_decay (𝓕 f) η x

theorem norm_partialFourier_le (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ‖partialFourier f η x‖ ≤
      partialFourierDecayConstant f * ((1 + x ^ 2)⁻¹ * (1 + η ^ 2)⁻¹) := by
  rw [← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < (1 + x ^ 2) * (1 + η ^ 2))).mpr
  nlinarith [partialFourier_product_decay f η x]

theorem partialFourier_gaussian_summable_norm (f : SchwartzMap ℂ ℂ) :
    Summable (fun p : ℤ × ℤ =>
      ‖partialFourier f (p.2 : ℝ) (p.1 : ℝ)‖) := by
  apply summable_norm_of_cauchy_product
    (fun p : ℤ × ℤ => partialFourier f (p.2 : ℝ) (p.1 : ℝ))
    (partialFourierDecayConstant f)
  intro p
  exact norm_partialFourier_le f (p.2 : ℝ) (p.1 : ℝ)

theorem partialFourier_gaussian_summable (f : SchwartzMap ℂ ℂ) :
    Summable (fun p : ℤ × ℤ => partialFourier f (p.2 : ℝ) (p.1 : ℝ)) :=
  (partialFourier_gaussian_summable_norm f).of_norm

theorem plane_lattice_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun p : ℤ × ℤ => ‖f (complexPoint (p.1 : ℝ) (p.2 : ℝ))‖) := by
  apply summable_norm_of_cauchy_product _ (planeDecayConstant f)
  intro p
  rw [← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity :
    0 < (1 + (p.1 : ℝ) ^ 2) * (1 + (p.2 : ℝ) ^ 2))).mpr
  nlinarith [plane_schwartz_product_decay f (p.1 : ℝ) (p.2 : ℝ)]

theorem plane_lattice_summable (f : 𝓢(ℂ, ℂ)) :
    Summable (fun p : ℤ × ℤ => f (complexPoint (p.1 : ℝ) (p.2 : ℝ))) :=
  (plane_lattice_summable_norm f).of_norm

theorem schwartz_poisson_zero (g : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, g (n : ℝ)) = ∑' n : ℤ, 𝓕 (g : ℝ → ℂ) (n : ℝ) := by
  simpa [fourier_eval_zero, SchwartzMap.fourier_coe] using g.tsum_eq_tsum_fourier 0

theorem vertical_poisson (f : 𝓢(ℂ, ℂ)) (x : ℝ) :
    (∑' n : ℤ, f (complexPoint x (n : ℝ))) =
      ∑' n : ℤ, partialFourier f (n : ℝ) x := by
  exact schwartz_poisson_zero (verticalSlice f x)

private theorem horizontal_poisson (f : 𝓢(ℂ, ℂ)) (n : ℤ) :
    (∑' m : ℤ, partialFourier f (n : ℝ) (m : ℝ)) =
      ∑' k : ℤ, (𝓕 f) (complexPoint (k : ℝ) (n : ℝ)) := by
  have h := schwartz_poisson_zero (partialFourierSchwartz f n)
  simpa only [partialFourierSchwartz_apply, partialFourierSchwartz_coe,
    fourier_partialFourier, SchwartzMap.fourier_coe] using h

private theorem iterated_poisson_pair_sum
    (f g h : ℤ → ℤ → ℂ)
    (hf : Summable (Function.uncurry f))
    (hg : Summable (Function.uncurry g))
    (hh : Summable (Function.uncurry h))
    (hvertical : ∀ m, (∑' n, f m n) = ∑' n, h m n)
    (hhorizontal : ∀ n, (∑' m, h m n) = ∑' m, g m n) :
    (∑' p : ℤ × ℤ, f p.1 p.2) = ∑' p : ℤ × ℤ, g p.1 p.2 := by
  calc
    (∑' p : ℤ × ℤ, f p.1 p.2) = ∑' m, ∑' n, f m n := hf.tsum_prod
    _ = ∑' m, ∑' n, h m n := tsum_congr hvertical
    _ = ∑' n, ∑' m, h m n := hh.tsum_comm.symm
    _ = ∑' n, ∑' m, g m n := tsum_congr hhorizontal
    _ = ∑' m, ∑' n, g m n := hg.tsum_comm
    _ = ∑' p : ℤ × ℤ, g p.1 p.2 := hg.tsum_prod.symm

theorem integer_pair_poisson (f : 𝓢(ℂ, ℂ)) :
    (∑' p : ℤ × ℤ, f (complexPoint (p.1 : ℝ) (p.2 : ℝ))) =
      ∑' p : ℤ × ℤ, (𝓕 f) (complexPoint (p.1 : ℝ) (p.2 : ℝ)) := by
  exact iterated_poisson_pair_sum
    (fun m n => f (complexPoint (m : ℝ) (n : ℝ)))
    (fun m n : ℤ => (𝓕 f : 𝓢(ℂ, ℂ)) (complexPoint (m : ℝ) (n : ℝ)))
    (fun m n => partialFourier f (n : ℝ) (m : ℝ))
    (plane_lattice_summable f) (plane_lattice_summable (𝓕 f))
    (partialFourier_gaussian_summable f)
    (fun m => vertical_poisson f m) (horizontal_poisson f)

end EisensteinSchwartzPoisson

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.EisensteinLattice
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace EisensteinSchwartzPoisson

section
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem integral_comp_linearEquiv (A : ℂ ≃L[ℝ] ℂ) (f : ℂ → ℂ) :
    (∫ x : ℂ, f (A x)) = inverseJacobian A • ∫ x : ℂ, f x := by
  have h := integral_map_equiv («μ» := (volume : Measure ℂ))
    A.toHomeomorph.toMeasurableEquiv f
  have hm : Measure.map A (volume : Measure ℂ) =
      ENNReal.ofReal (inverseJacobian A) • volume := by
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume
      A.toLinearEquiv.isUnit_det'.ne_zero
  change (∫ y : ℂ, f y ∂Measure.map A volume) = (∫ x : ℂ, f (A x)) at h
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal (show 0 ≤ inverseJacobian A from abs_nonneg _)] at h
  exact h.symm

theorem inner_linear_dual (A : ℂ ≃L[ℝ] ℂ) (x y : ℂ) :
    inner ℝ (A x) (dualMap A y) = inner ℝ x y := by
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  simp

theorem fourier_comp_linearEquiv (A : ℂ ≃L[ℝ] ℂ) (f : ℂ → ℂ) (w : ℂ) :
    𝓕 (f ∘ A) w = inverseJacobian A • 𝓕 f (dualMap A w) := by
  let H : ℂ → ℂ := fun z => Real.fourierChar (-inner ℝ z (dualMap A w)) • f z
  calc
    𝓕 (f ∘ A) w = ∫ x : ℂ, H (A x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [H, inner_linear_dual, Function.comp_apply]
        rfl
    _ = inverseJacobian A • ∫ z : ℂ, H z := integral_comp_linearEquiv A H
    _ = inverseJacobian A • 𝓕 f (dualMap A w) := rfl

theorem fourier_translate (f : ℂ → ℂ) (b w : ℂ) :
    𝓕 (fun z => f (z + b)) w =
      Real.fourierChar (inner ℝ b w) • 𝓕 f w := by
  exact congrFun
    (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure ℂ) (innerₗ ℂ) f b) w

theorem fourier_affinePullback (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b w : ℂ) :
    (𝓕 (affinePullback f A b)) w =
      inverseJacobian A •
        (Real.fourierChar (inner ℝ b (dualMap A w)) • (𝓕 f) (dualMap A w)) := by
  rw [congrFun (SchwartzMap.fourier_coe _) w]
  change 𝓕 ((fun z => f (z + b)) ∘ A) w = _
  rw [fourier_comp_linearEquiv, fourier_translate]
  rw [congrFun (SchwartzMap.fourier_coe f) (dualMap A w)]

theorem affine_lattice_poisson (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) :
    (∑' p : ℤ × ℤ, f (A (complexPoint (p.1 : ℝ) (p.2 : ℝ)) + b)) =
      inverseJacobian A • ∑' p : ℤ × ℤ,
        Real.fourierChar (inner ℝ b (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) •
          (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))) := by
  have h := integer_pair_poisson (affinePullback f A b)
  simp only [affinePullback_apply, fourier_affinePullback] at h
  rw [tsum_const_smul''] at h
  exact h

end

section
open MeasureTheory EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem eisensteinLatticeMap_point (c : ℂ) (hc : c ≠ 0) (p : ℤ × ℤ) :
    eisensteinLatticeMap c hc (complexPoint (p.1 : ℝ) (p.2 : ℝ)) =
      c * eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) := by
  simp [eisensteinLatticeMap, complexPoint, eisEmbedding_eval, mul_comm]

theorem actual_eisenstein_coset_poisson (f : 𝓢(ℂ, ℂ)) (b c : O) (hc : c ≠ 0) :
    (∑' z : O, f (eisEmbedding (b + c * z))) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
        Real.fourierChar (inner ℝ (eisEmbedding b)
          (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
        (𝓕 f) (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p) := by
  let A := eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc)
  have h := affine_lattice_poisson f A (eisEmbedding b)
  rw [eisenstein_inverseJacobian] at h
  calc
    (∑' z : O, f (eisEmbedding (b + c * z))) =
        ∑' p : ℤ × ℤ, f (eisEmbedding (b + c * latticeCoordEquiv.symm p)) :=
      (latticeCoordEquiv.symm.tsum_eq _).symm
    _ = ∑' p : ℤ × ℤ,
        f (A (complexPoint (p.1 : ℝ) (p.2 : ℝ)) + eisEmbedding b) := by
      apply tsum_congr
      intro p
      congr 1
      rw [map_add, map_mul]
      change eisEmbedding b + eisEmbedding c *
          eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) = _
      rw [← eisensteinLatticeMap_point]
      exact add_comm _ _
    _ = _ := h

theorem actual_eisenstein_coset_summable_norm (f : 𝓢(ℂ, ℂ)) (b c : O) (hc : c ≠ 0) :
    Summable (fun z : O => ‖f (eisEmbedding (b + c * z))‖) := by
  let A := eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc)
  have hp := plane_lattice_summable_norm (affinePullback f A (eisEmbedding b))
  have hpair : Summable (fun p : ℤ × ℤ =>
      ‖f (eisEmbedding (b + c * latticeCoordEquiv.symm p))‖) := by
    convert (preTransparency := .instances) hp using 1
    funext p
    rw [affinePullback_apply]
    apply congrArg norm
    apply congrArg f
    rw [map_add, map_mul]
    change eisEmbedding b + eisEmbedding c *
        eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) = _
    rw [← eisensteinLatticeMap_point]
    exact add_comm _ _
  exact (latticeCoordEquiv.symm.summable_iff).mp hpair

theorem actual_eisenstein_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun z : O => ‖f (eisEmbedding z)‖) := by
  simpa using actual_eisenstein_coset_summable_norm f 0 1 one_ne_zero

theorem actual_eisenstein_periodic_summable (f : 𝓢(ℂ, ℂ))
    {R : Type*} [Fintype R] (q : O → R) (P : R → ℂ) :
    Summable (fun z : O => P (q z) * f (eisEmbedding z)) := by
  classical
  let C : ℝ := ∑ r : R, ‖P r‖
  have hP (r : R) : ‖P r‖ ≤ C :=
    Finset.single_le_sum (fun a _ => norm_nonneg (P a)) (Finset.mem_univ r)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _
    ((actual_eisenstein_summable_norm f).mul_left C)
  intro z
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hP (q z)) (norm_nonneg _)

theorem actual_eisenstein_periodic_poisson (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      ∑ r : O ⧸ Ideal.span {c}, P r *
        ((2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
          Real.fourierChar (inner ℝ
            (eisEmbedding (GaussianShiftedPartition.representative c r))
            (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
          (𝓕 f) (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [GaussianAbelPartition.tsum_periodic_weighted_partition
    (Ideal.Quotient.mk (Ideal.span {c})) P (fun z => f (eisEmbedding z))
    (actual_eisenstein_periodic_summable f _ P)]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  exact (GaussianFiberEquiv.fiber_tsum c hc r
    (GaussianShiftedPartition.representative c r)
    (GaussianShiftedPartition.representative_spec c r)
    (fun z => f (eisEmbedding z))).trans
      (actual_eisenstein_coset_poisson f _ c hc)

theorem inverseJacobian_pos (A : ℂ ≃L[ℝ] ℂ) : 0 < inverseJacobian A :=
  abs_pos.mpr (inv_ne_zero A.toLinearEquiv.isUnit_det'.ne_zero)

theorem dual_lattice_summable_norm (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) :
    Summable (fun p : ℤ × ℤ =>
      ‖(𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))‖) := by
  have hJ := inverseJacobian_pos A
  have hp := plane_lattice_summable_norm (𝓕 (affinePullback f A 0))
  have hn (p : ℤ × ℤ) :
      ‖(𝓕 (affinePullback f A 0)) (complexPoint (p.1 : ℝ) (p.2 : ℝ))‖ =
      inverseJacobian A * ‖(𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))‖ := by
    rw [fourier_affinePullback]
    simp [ abs_of_pos hJ]
  simp_rw [hn] at hp
  have hi := hp.mul_left (inverseJacobian A)⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hJ.ne', one_mul] using hi

theorem finite_phase_sum {R : Type*} [Fintype R]
    (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b : R → ℂ) (P : R → ℂ) :
    (∑ r : R, P r * (inverseJacobian A • ∑' p : ℤ × ℤ,
      Real.fourierChar (inner ℝ (b r) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) •
        (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))))) =
    inverseJacobian A • ∑' p : ℤ × ℤ,
      (∑ r : R, P r * (Real.fourierChar (inner ℝ (b r)
        (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) : ℂ)) *
        (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))) := by
  classical
  have hs (r : R) : Summable (fun p : ℤ × ℤ =>
      P r * (Real.fourierChar (inner ℝ (b r)
        (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) •
        (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))))) := by
    apply Summable.mul_left
    apply Summable.of_norm
    simpa only [Circle.norm_smul] using dual_lattice_summable_norm f A
  simp_rw [mul_smul_comm, ← tsum_mul_left]
  rw [← Finset.smul_sum, ← Summable.tsum_finsetSum (fun r _ => hs r)]
  congr 1
  apply tsum_congr
  intro p
  simp only [Circle.smul_def, smul_eq_mul, Finset.sum_mul, mul_assoc]

theorem actual_eisenstein_periodic_fourier (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          (Real.fourierChar (inner ℝ
            (eisEmbedding (GaussianShiftedPartition.representative c r))
            (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) : ℂ)) *
          (𝓕 f) (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [actual_eisenstein_periodic_poisson f c hc P]
  have h := finite_phase_sum f
    (eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc))
    (fun r => eisEmbedding (GaussianShiftedPartition.representative c r)) P
  rw [eisenstein_inverseJacobian] at h
  exact h

end

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem dualMap_trans (A B : ℂ ≃L[ℝ] ℂ) (z : ℂ) :
    dualMap (A.trans B) z = dualMap B (dualMap A z) := by
  change (ContinuousLinearMap.adjoint
    (A.symm.toContinuousLinearMap.comp B.symm.toContinuousLinearMap)) z = _
  rw [ContinuousLinearMap.adjoint_comp]
  rfl

theorem dual_basis_apply (w : ℂ) (hw : w.im ≠ 0) (z : ℂ) :
    dualMap (basisEquiv w hw) z =
      complexPoint z.re ((z.im - w.re * z.re) / w.im) := by
  apply ext_inner_left ℝ
  intro v
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ ((basisEquiv w hw).symm v) z = _
  simp only [basisEquiv_symm_apply, Complex.inner, complexPoint,
    Complex.mul_re,  Complex.conj_re, Complex.conj_im]
  field_simp [hw]
  ring

theorem dual_mul_apply (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    dualMap (complexMulEquiv c hc) z = (starRingEnd ℂ c)⁻¹ * z := by
  apply ext_inner_left ℝ
  intro v
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (c⁻¹ * v) z = _
  simp only [Complex.inner, map_mul, map_inv₀]
  congr 1
  ring

theorem eisensteinDualFrequency_explicit (c : ℂ) (hc : c ≠ 0) (p : ℤ × ℤ) :
    eisensteinDualFrequency c hc p =
      complexPoint (p.1 : ℝ) (((p.1 : ℝ) + 2 * (p.2 : ℝ)) / Real.sqrt 3) /
        starRingEnd ℂ c := by
  unfold eisensteinDualFrequency eisensteinLatticeMap scaledBasisEquiv
  rw [dualMap_trans, dual_basis_apply, dual_mul_apply]
  have he : complexPoint (complexPoint (p.1 : ℝ) (p.2 : ℝ)).re
      (((complexPoint (p.1 : ℝ) (p.2 : ℝ)).im - omega3.re *
        (complexPoint (p.1 : ℝ) (p.2 : ℝ)).re) / omega3.im) =
      complexPoint (p.1 : ℝ) (((p.1 : ℝ) + 2 * (p.2 : ℝ)) / Real.sqrt 3) := by
    apply Complex.ext
    · rfl
    · simp only [complexPoint, omega3_im]
      have hr : omega3.re = -(1 / 2 : ℝ) := by norm_num [omega3]
      rw [hr]
      ring
  rw [he]
  ring

theorem actual_eisenstein_poisson_explicit (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          (Real.fourierChar (inner ℝ
            (eisEmbedding (GaussianShiftedPartition.representative c r))
            (explicitDualFrequency (eisEmbedding c) p)) : ℂ)) *
          (𝓕 f) (explicitDualFrequency (eisEmbedding c) p) := by
  simpa only [eisensteinDualFrequency_explicit, explicitDualFrequency] using
    actual_eisenstein_periodic_fourier f c hc P

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

end EisensteinSchwartzPoisson

open scoped BigOperators Classical

namespace IdealGaussCRT

theorem gauss_transform_finite_crt_scalar {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, Field (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i)
    (χ : ∀ i, MulChar (R i) ℂ) (ψ : AddChar T ℂ)
    (hχ : ∀ i, χ i ≠ 1) (h : T) :
    (∑ x : T, (∏ i, χ i (e x i)) * ψ (h * x)) =
      (∏ i, χ i (e h i))⁻¹ *
        ∑ x : T, (∏ i, χ i (e x i)) * ψ x := by
  classical
  have hbase := gauss_transform_finite_crt R e χ ψ hχ (1 : T)
  simp only [one_mul, map_one, Pi.one_apply, one_ne_zero, ↓reduceIte,
    inv_one, one_mul] at hbase
  rw [gauss_transform_finite_crt R e χ ψ hχ h, hbase]
  have hlocal (i : ι) :
      (if e h i = 0 then 0 else
        (χ i (e h i))⁻¹ * gaussSum (χ i) (coordinateAddChar R e ψ i)) =
      (χ i (e h i))⁻¹ * gaussSum (χ i) (coordinateAddChar R e ψ i) := by
    split_ifs with hi
    · simp [hi]
    · rfl
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]

end IdealGaussCRT

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace ActualEisensteinCubic

theorem canonical_finite_prime_gauss_transform_scalar
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) (h : O ⧸ ∏ i, P i) :
    (∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ (h * x)) =
      (finiteSexticQuotientRow P hc hgood j h)⁻¹ *
        ∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ x := by
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
  exact IdealGaussCRT.gauss_transform_finite_crt_scalar (fun i => O ⧸ P i)
    (IdealGaussCRT.quotientProdEquivPi P hc)
    (fun i => canonicalSextic (P i) (hgood i) ^ j i) ψ
    (fun i => canonicalSextic_pow_ne_one (P i) (hgood i) (hchar i) (hj0 i) (hj6 i)) h

theorem finiteSexticQuotientRow_inv_eq_star
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (h : O ⧸ ∏ i, P i) :
    (finiteSexticQuotientRow P hc hgood j h)⁻¹ =
      star (finiteSexticQuotientRow P hc hgood j h) := by
  classical
  simp only [finiteSexticQuotientRow, star_prod]
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']

theorem canonical_finite_prime_gauss_transform_conj
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) (h : O ⧸ ∏ i, P i) :
    (∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ (h * x)) =
      star (finiteSexticQuotientRow P hc hgood j h) *
        ∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ x := by
  rw [canonical_finite_prime_gauss_transform_scalar P hc hgood hchar j hj0 hj6 ψ,
    finiteSexticQuotientRow_inv_eq_star]

end ActualEisensteinCubic

namespace EisensteinSchwartzPoisson

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem explicitDualFrequency_eq_paperFrequency (c : ℂ) (p : ℤ × ℤ) :
    explicitDualFrequency c p = paperFrequency (eisEmbedding (dualFrequencyEquiv p) / c) := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hnum : complexPoint (p.1 : ℝ)
      (((p.1 : ℝ) + 2 * (p.2 : ℝ)) / Real.sqrt 3) =
      (2 * Complex.I / (Real.sqrt 3 : ℂ)) *
        starRingEnd ℂ (eisEmbedding (dualFrequencyEquiv p)) := by
    rw [dualFrequencyEquiv_coordinates]
    apply Complex.ext <;>
      norm_num [complexPoint, Complex.div_re, Complex.div_im] <;>
      field_simp <;>
      simp only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  unfold explicitDualFrequency paperFrequency
  rw [map_div₀, hnum]
  ring

theorem explicitDualFrequency_phase (r c : ℂ) (p : ℤ × ℤ) :
    (Real.fourierChar (inner ℝ r (explicitDualFrequency c p)) : ℂ) =
      paperE (r * eisEmbedding (dualFrequencyEquiv p) / c) := by
  rw [explicitDualFrequency_eq_paperFrequency, fourierChar_paperFrequency]
  congr 1
  ring

theorem actual_eisenstein_paper_poisson (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          paperE (eisEmbedding (GaussianShiftedPartition.representative c r) *
            eisEmbedding h / eisEmbedding c)) *
          paperFourier f (eisEmbedding h / eisEmbedding c) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let A : O → ℂ := fun h => ∑ r : O ⧸ Ideal.span {c}, P r *
    paperE (eisEmbedding (GaussianShiftedPartition.representative c r) *
      eisEmbedding h / eisEmbedding c)
  have ht : (∑' h : O, A h * paperFourier f (eisEmbedding h / eisEmbedding c)) =
      (2 / Real.sqrt 3 : ℝ) • ∑' p : ℤ × ℤ,
        A (dualFrequencyEquiv p) *
          (𝓕 f) (explicitDualFrequency (eisEmbedding c) p) := by
    calc
      _ = ∑' p : ℤ × ℤ, A (dualFrequencyEquiv p) *
          paperFourier f (eisEmbedding (dualFrequencyEquiv p) / eisEmbedding c) :=
        (dualFrequencyEquiv.tsum_eq _).symm
      _ = ∑' p : ℤ × ℤ, (2 / Real.sqrt 3 : ℝ) •
          (A (dualFrequencyEquiv p) *
            (𝓕 f) (explicitDualFrequency (eisEmbedding c) p)) := by
        apply tsum_congr
        intro p
        rw [paperFourier_eq_standard, ← explicitDualFrequency_eq_paperFrequency]
        change A (dualFrequencyEquiv p) *
          ((2 / Real.sqrt 3 : ℝ) • (𝓕 f) (explicitDualFrequency (eisEmbedding c) p)) = _
        simp only [Algebra.smul_def]
        ring
      _ = _ := tsum_const_smul'' _
    rfl
  have hp := actual_eisenstein_poisson_explicit f c hc P
  simp_rw [explicitDualFrequency_phase] at hp
  change _ = (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) •
    ∑' h : O, A h * paperFourier f (eisEmbedding h / eisEmbedding c)
  rw [ht, smul_smul]
  convert (preTransparency := .instances) hp using 1
  congr 1
  ring

theorem actual_eisenstein_paper_poisson_trace (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          paperFourier f (eisEmbedding h / eisEmbedding c) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  simpa only [eisTraceModChar_frequency] using actual_eisenstein_paper_poisson f c hc P

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

theorem paperFourier_comp_mul (f : ℂ → ℂ) (a : ℂ) (ha : a ≠ 0) (u : ℂ) :
    paperFourier (fun z => f (a * z)) u =
      (1 / ‖a‖ ^ 2 : ℝ) • paperFourier f (u / a) := by
  have hd : dualMap (complexMulEquiv a ha) (paperFrequency u) =
      paperFrequency (u / a) := by
    rw [dual_mul_apply]
    unfold paperFrequency
    rw [map_div₀]
    ring
  have hj : inverseJacobian (complexMulEquiv a ha) = 1 / ‖a‖ ^ 2 := by
    rw [inverseJacobian, complexMulEquiv_det, abs_inv,
      abs_of_nonneg (Complex.normSq_nonneg a), Complex.sq_norm]
    ring
  rw [paperFourier_eq_standard, paperFourier_eq_standard]
  have hF := fourier_comp_linearEquiv (complexMulEquiv a ha) f (paperFrequency u)
  simp only [Function.comp_def, complexMulEquiv_apply] at hF
  rw [hF, hd, hj, smul_smul, smul_smul]
  congr 1
  ring

theorem paperFourier_radial (W : ℝ → ℂ) (u : ℂ) :
    paperFourier (fun z => W (‖z‖ ^ 2)) u =
      paperRadialFourier W (‖u‖ ^ 2) := by
  unfold paperRadialFourier
  rw [Real.sqrt_sq (norm_nonneg u)]
  by_cases hu : u = 0
  · simp [hu]
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hnC : (‖u‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  let a : ℂ := u / (‖u‖ : ℂ)
  have ha : a ≠ 0 := div_ne_zero hu hnC
  have hna : ‖a‖ = 1 := by
    simp [a, Complex.norm_real, hn]
  have hq : u / a = (‖u‖ : ℂ) := by
    dsimp [a]
    field_simp
  have hfun : (fun z : ℂ => W (‖a * z‖ ^ 2)) = fun z : ℂ => W (‖z‖ ^ 2) := by
    funext z
    rw [norm_mul, hna, one_mul]
  have hF := paperFourier_comp_mul (fun z => W (‖z‖ ^ 2)) a ha u
  rw [hfun, hna, hq] at hF
  simpa using hF

theorem inverseSqrt_norm_sq (K : ℝ) (hK : 0 < K) :
    ‖(Real.sqrt K : ℂ)⁻¹‖ ^ 2 = 1 / K := by
  rw [norm_inv, inv_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg K), Real.sq_sqrt hK.le, one_div]

theorem paperFourier_radial_scaled (W : ℝ → ℂ) (K : ℝ) (hK : 0 < K) (u : ℂ) :
    paperFourier (fun z => W (‖z‖ ^ 2 / K)) u =
      K • paperRadialFourier W (K * ‖u‖ ^ 2) := by
  let a : ℂ := (Real.sqrt K : ℂ)⁻¹
  have ha : a ≠ 0 := inverseSqrt_ne_zero K hK
  have hna : ‖a‖ ^ 2 = 1 / K := inverseSqrt_norm_sq K hK
  have hfun : (fun z : ℂ => W (‖a * z‖ ^ 2)) =
      fun z : ℂ => W (‖z‖ ^ 2 / K) := by
    funext z
    rw [norm_mul, mul_pow, hna]
    congr 1
    ring
  have hnorm : ‖u / a‖ ^ 2 = K * ‖u‖ ^ 2 := by
    rw [norm_div, div_pow, hna]
    field_simp
  have hF := paperFourier_comp_mul (fun z => W (‖z‖ ^ 2)) a ha u
  rw [hfun, hna, one_div_one_div, paperFourier_radial, hnorm] at hF
  exact hF

@[simp] theorem scaledRadialTest_apply (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (z : ℂ) :
    scaledRadialTest W K hK z = W (‖z‖ ^ 2 / K) := by
  simp only [scaledRadialTest, affinePullback_apply, complexMulEquiv_apply,
    add_zero, radialTest_apply, norm_mul, mul_pow, inverseSqrt_norm_sq K hK]
  congr 1
  ring

theorem paperFourier_scaledRadialTest (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (u : ℂ) :
    paperFourier (scaledRadialTest W K hK) u =
      K • paperRadialFourier W (K * ‖u‖ ^ 2) := by
  change paperFourier (fun z => scaledRadialTest W K hK z) u = _
  simp only [scaledRadialTest_apply]
  exact paperFourier_radial_scaled W K hK u

theorem actual_radial_paper_poisson_trace (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K)
    (c : O) (hc : c ≠ 0) (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      (K / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  let A : O → ℂ := fun h => ∑ r : O ⧸ Ideal.span {c}, P r *
    ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)
  have ht : (∑' h : O, A h *
      paperFourier (scaledRadialTest W K hK) (eisEmbedding h / eisEmbedding c)) =
      K • ∑' h : O, A h *
        paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
    calc
      _ = ∑' h : O, K • (A h *
          paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)) := by
        apply tsum_congr
        intro h
        rw [paperFourier_scaledRadialTest, norm_div, div_pow]
        have hr : K * (‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) =
            K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2 := by ring
        rw [hr]
        simp only [Algebra.smul_def]
        ring
      _ = _ := tsum_const_smul'' _
  have hp := actual_eisenstein_paper_poisson_trace (scaledRadialTest W K hK) c hc P
  change (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) *
    scaledRadialTest W K hK (eisEmbedding z)) =
    (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O, A h *
      paperFourier (scaledRadialTest W K hK) (eisEmbedding h / eisEmbedding c) at hp
  rw [ht, smul_smul] at hp
  simpa only [scaledRadialTest_apply, one_div_mul_eq_div] using hp

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

namespace ActualEisensteinCubic
open ConcreteTraceCRT EisensteinSchwartzPoisson

theorem finitePrimeModulus_norm_sq {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) :
    ‖eisEmbedding (finitePrimeModulus P)‖ ^ 2 = (Ideal.absNorm (∏ i, P i) : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span, span_finitePrimeModulus]

theorem canonical_principal_gauss_transform {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (c : O) (hc : Ideal.span {c} = ∏ i, P i)
    [Fintype (O ⧸ Ideal.span {c})]
    (ψ : AddChar (O ⧸ Ideal.span {c}) ℂ) (h : O ⧸ Ideal.span {c}) :
    (∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r * ψ (h * r)) =
      star (principalSexticRow P hcop hgood j c hc h) *
        ∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r * ψ r := by
  let e := Ideal.quotEquivOfEq hc
  let row := finiteSexticQuotientRow P hcop hgood j
  let φ : AddChar (O ⧸ ∏ i, P i) ℂ := ψ.compAddMonoidHom e.symm.toAddMonoidHom
  have hleft :
      (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ (h * r)) =
        ∑ x : O ⧸ ∏ i, P i, row x * φ (e h * x) := by
    rw [← Equiv.sum_comp e.toEquiv (fun x => row x * φ (e h * x))]
    apply Finset.sum_congr rfl
    intro r _
    change row (e r) * ψ (h * r) = row (e r) * ψ (e.symm (e h * e r))
    rw [← map_mul, e.symm_apply_apply]
  have hbase :
      (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ r) =
        ∑ x : O ⧸ ∏ i, P i, row x * φ x := by
    rw [← Equiv.sum_comp e.toEquiv (fun x => row x * φ x)]
    apply Finset.sum_congr rfl
    intro r _
    change row (e r) * ψ r = row (e r) * ψ (e.symm (e r))
    rw [e.symm_apply_apply]
  change (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ (h * r)) =
    star (row (e h)) * ∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ r
  rw [hleft, hbase]
  exact canonical_finite_prime_gauss_transform_conj P hcop hgood hchar j hj0 hj6 φ (e h)

theorem canonical_radial_poisson {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus P
    let hc0 := finitePrimeModulus_ne_zero P
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let row := principalSexticRow P hcop hgood j c (span_finitePrimeModulus P)
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc0
    (∑' z : O, finiteSexticRow P hgood j z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
      (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (star (finiteSexticRow P hgood j h) * (∑ r, row r * ψ r)) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  classical
  let c := finitePrimeModulus P
  have hc0 : c ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (span_finitePrimeModulus P)
  let : Fintype (O ⧸ ∏ i, P i) := Fintype.ofEquiv (O ⧸ Ideal.span {c}) e.toEquiv
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let row := principalSexticRow P hcop hgood j c (span_finitePrimeModulus P)
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc0
  have ht (h : O) :
      (∑ r : O ⧸ Ideal.span {c}, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) =
        star (finiteSexticRow P hgood j h) * (∑ r, row r * ψ r) := by
    rw [canonical_principal_gauss_transform P hcop hgood hchar j hj0 hj6 c
      (span_finitePrimeModulus P) ψ, principalSexticRow_mk]
  have hp := actual_radial_paper_poisson_trace W scale hscale c hc0 row
  change (∑' z : O, row (Ideal.Quotient.mk (Ideal.span {c}) z) *
    W (‖eisEmbedding z‖ ^ 2 / scale)) =
      (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, row r *
          ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  simp_rw [ht] at hp
  simpa only [row, principalSexticRow_mk] using hp

theorem canonical_radial_poisson_normalized {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus P
    (∑' z : O, finiteSexticRow P hgood j z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * canonicalNormalizedGauss P hcop hgood j / (‖eisEmbedding c‖ : ℂ)) *
        ∑' h : O, star (finiteSexticRow P hgood j h) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  classical
  let c := finitePrimeModulus P
  let G := canonicalGaussSum P hcop hgood j
  let F : O → ℂ := fun h => star (finiteSexticRow P hgood j h) *
    paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)
  have hp := canonical_radial_poisson P hcop hgood hchar j hj0 hj6 W scale hscale
  change (∑' z : O, finiteSexticRow P hgood j z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
    (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
      (star (finiteSexticRow P hgood j h) * G) *
        paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  have hsum : (∑' h : O, (star (finiteSexticRow P hgood j h) * G) *
      paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)) =
      G * ∑' h : O, F h := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro h
    dsimp [F]
    ring
  rw [hsum] at hp
  rw [hp]
  change ((scale / ‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) * (G * ∑' h : O, F h) =
    ((scale : ℂ) * (G / (‖eisEmbedding c‖ : ℂ)) / (‖eisEmbedding c‖ : ℂ)) *
      ∑' h : O, F h
  have hn : (‖eisEmbedding c‖ : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr
      (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P)))
  push_cast
  field_simp

theorem finiteSexticRow_radial_summable {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    Summable (fun z : O => finiteSexticRow P hgood j z *
      W (‖eisEmbedding z‖ ^ 2 / scale)) := by
  let c := finitePrimeModulus P
  have hc0 : c ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  have hs := actual_eisenstein_periodic_summable (scaledRadialTest W scale hscale)
    (Ideal.Quotient.mk (Ideal.span {c}))
    (principalSexticRow P hcop hgood j c (span_finitePrimeModulus P))
  simpa only [principalSexticRow_mk, scaledRadialTest_apply] using hs

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.RadialFourier
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace EisensteinSchwartzPoisson

open ConcreteTraceCRT ActualEisensteinCubic
open scoped SchwartzMap

theorem polynomial_tail_majorant (A : ℕ) (K T q B f : ℝ)
    (hK : 0 < K) (hT : 0 ≤ T) (hq : 0 ≤ q) (hf : 0 ≤ f)
    (htail : T ≤ K * q) (hbound : (1 + K * q) ^ (A + 2) * f ≤ B) :
    f ≤ (B / ((min 1 K) ^ 2 * (1 + T) ^ A)) * ((1 + q) ^ 2)⁻¹ := by
  have hm : 0 < min 1 K := lt_min (by norm_num) hK
  have hm1 : min 1 K ≤ 1 := min_le_left _ _
  have hmK : min 1 K ≤ K := min_le_right _ _
  have hbase : min 1 K * (1 + q) ≤ 1 + K * q := by
    nlinarith [mul_le_mul_of_nonneg_right hmK hq]
  have htwo : (min 1 K) ^ 2 * (1 + q) ^ 2 ≤ (1 + K * q) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hpow : (1 + T) ^ A ≤ (1 + K * q) ^ A :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hden : ((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2 ≤
      (1 + K * q) ^ (A + 2) := by
    have hh := mul_le_mul hpow htwo (by positivity) (by positivity)
    rw [pow_add]
    nlinarith
  have hprod : f * (((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2) ≤ B := by
    calc
      _ = (((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2) * f := mul_comm _ _
      _ ≤ (1 + K * q) ^ (A + 2) * f := mul_le_mul_of_nonneg_right hden hf
      _ ≤ B := hbound
  have hraw := (le_div_iff₀ (show 0 < ((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2
      by positivity)).mpr hprod
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using hraw

theorem paperRadialFourier_lattice_summable_norm (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun h : O => ‖paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)‖) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound 2
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let D := (min 1 K) ^ 2 * (1 + (0 : ℝ)) ^ (0 : ℕ)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (eisenstein_cauchy_summable.mul_left (B / D))
  intro h
  exact polynomial_tail_majorant 0 K 0 _ B _ hK (by norm_num)
    (sq_nonneg _) (norm_nonneg _) (by positivity) (hb W _ (by positivity))

theorem paperRadialFourier_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K T : ℝ), 0 < K → 0 ≤ T →
        (∑' h : {h : O // T ≤ K * ‖eisEmbedding h‖ ^ 2},
          ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
        (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound (A + 2)
  refine ⟨s, C * (eisensteinCauchyMass + 1), by
    have := eisensteinCauchyMass_nonneg
    positivity, ?_⟩
  intro W K T hK hT
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let D := (min 1 K) ^ 2 * (1 + T) ^ A
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hm : 0 < min 1 K := lt_min (by norm_num) hK
  have hD : 0 < D := by dsimp [D]; positivity
  let S := {h : O | T ≤ K * ‖eisEmbedding h‖ ^ 2}
  have hp (h : S) :
      ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
        (B / D) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := by
    exact polynomial_tail_majorant A K T _ B _ hK hT (sq_nonneg _)
      (norm_nonneg _) h.property (hb W _ (by positivity))
  have hmajor : Summable (fun h : S => (B / D) *
      ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) :=
    (eisenstein_cauchy_summable.subtype S).mul_left (B / D)
  have hs : Summable (fun h : S =>
      ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp hmajor
  calc
    _ ≤ ∑' h : S, (B / D) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ :=
      hs.tsum_le_tsum hp hmajor
    _ = (B / D) * ∑' h : S, ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := tsum_mul_left
    _ ≤ (B / D) * eisensteinCauchyMass :=
      mul_le_mul_of_nonneg_left (eisensteinCauchyMass_subtype S) (div_nonneg hB hD.le)
    _ ≤ (B / D) * (eisensteinCauchyMass + 1) := by
      gcongr
      linarith
    _ = _ := by dsimp [B, D]; ring

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.IdealGenerators
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace ConcretePrimeRowBridge

theorem tsum_ideal_eq_tsum_generator (J : Ideal O) (hJ : J ≠ ⊥)
    (f : O → ℂ) :
    (∑' u : O, if u ∈ J then f u else 0) =
      ∑' z : O, f (idealGenerator J * z) := by
  let d := idealGenerator J
  have hd : d ≠ 0 := idealGenerator_ne_zero J hJ
  let F : O → ℂ := fun u => if u ∈ J then f u else 0
  have hrange : Function.support F ⊆ Set.range (fun z : O => d * z) := by
    intro u hu
    have huJ : u ∈ J := by
      by_contra hn
      exact hu (by simp [F, hn])
    rw [← span_idealGenerator J, Ideal.mem_span_singleton] at huJ
    obtain ⟨z, hz⟩ := huJ
    exact ⟨z, hz.symm⟩
  have ht := (mul_right_injective₀ hd).tsum_eq hrange
  calc
    (∑' u : O, if u ∈ J then f u else 0) = ∑' z : O, F (d * z) := ht.symm
    _ = ∑' z : O, f (d * z) := by
      apply tsum_congr
      intro z
      have hz : d * z ∈ J := by
        rw [← span_idealGenerator J, Ideal.mem_span_singleton]
        exact ⟨z, rfl⟩
      simp only [F, if_pos hz]

end ConcretePrimeRowBridge

namespace ActualEisensteinCubic

theorem tsum_rowCoprimeMask_subsets
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι)
    (f : O → ℂ) (hf : Summable f) :
    (∑' u : O, rowCoprimeMask P S u * f u) =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card *
        ∑' u : O, if ∀ i ∈ E, u ∈ P i then f u else 0 := by
  have hterm (u : O) : rowCoprimeMask P S u * f u =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card *
        (if ∀ i ∈ E, u ∈ P i then f u else 0) := by
    rw [rowCoprimeMask_subsets, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro E hE
    by_cases h : ∀ i ∈ E, u ∈ P i <;> simp [h]
  have hsum (E : Finset ι) :
      Summable (fun u : O => (-1 : ℂ) ^ E.card *
        (if ∀ i ∈ E, u ∈ P i then f u else 0)) := by
    have hi := hf.indicator {u : O | ∀ i ∈ E, u ∈ P i}
    simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using hi.mul_left ((-1 : ℂ) ^ E.card)
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun E _ => hsum E)]
  apply Finset.sum_congr rfl
  intro E hE
  exact tsum_mul_left

theorem primeSubsetGenerator_ne_zero {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (E : Finset ι) :
    primeSubsetGenerator P E ≠ 0 := by
  apply ConcretePrimeRowBridge.idealGenerator_ne_zero
  change (∏ i ∈ E, P i) ≠ 0
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i))

theorem tsum_rowCoprimeMask_dilations
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (f : O → ℂ) (hf : Summable f) :
    (∑' u : O, rowCoprimeMask P S u * f u) =
      ∑ E ∈ S.powerset,
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
          ∑' z : O, f (primeSubsetGenerator P E * z) := by
  rw [tsum_rowCoprimeMask_subsets P S f hf]
  have hprime (i : ι) : Prime (P i) :=
    Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
  apply Finset.sum_congr rfl
  intro E hE
  rw [prime_product_moebius P hprime hinj E]
  congr 1
  have hJ : (∏ i ∈ E, P i) ≠ ⊥ := by
    change (∏ i ∈ E, P i) ≠ 0
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i))
  calc
    _ = ∑' u : O, if u ∈ (∏ i ∈ E, P i) then f u else 0 := by
      apply tsum_congr
      intro u
      rw [mem_prime_product_iff P hinj E u]
      by_cases h : ∀ i ∈ E, u ∈ P i <;> simp [h]
    _ = _ := ConcretePrimeRowBridge.tsum_ideal_eq_tsum_generator _ hJ f

open ConcreteTraceCRT

theorem tsum_masked_radial_dilations
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hinj : Function.Injective P) (S : Finset ι)
    (r : O → ℂ) (hr : ∀ a b, r (a * b) = r a * r b)
    (W : ℝ → ℂ) (scale : ℝ)
    (hsum : Summable (fun u : O => r u * W (‖eisEmbedding u‖ ^ 2 / scale))) :
    (∑' u : O, rowCoprimeMask P S u * r u * W (‖eisEmbedding u‖ ^ 2 / scale)) =
      ∑ E ∈ S.powerset,
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
          r (primeSubsetGenerator P E) *
          ∑' z : O, r z *
            W (‖eisEmbedding z‖ ^ 2 / (scale / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2)) := by
  calc
    _ = ∑' u : O, rowCoprimeMask P S u *
        (r u * W (‖eisEmbedding u‖ ^ 2 / scale)) := by
      apply tsum_congr
      intro u
      ring
    _ = _ := by
      rw [tsum_rowCoprimeMask_dilations P hinj S _ hsum]
      apply Finset.sum_congr rfl
      intro E hE
      rw [mul_assoc]
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro z
      rw [hr, map_mul, norm_mul, mul_pow, div_div_eq_mul_div]
      ring_nf

open ConcreteTraceCRT EisensteinSchwartzPoisson

theorem primeSubset_reducedScale_pos {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (E : Finset α)
    {scale : ℝ} (hscale : 0 < scale) :
    0 < scale / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 := by
  exact div_pos hscale (sq_pos_of_pos (norm_pos_iff.mpr
    (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E))))

theorem canonical_masked_radial_dilations
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (S : Finset α)
    (Q : ι → Ideal O) [∀ i, (Q i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime Q))
    (hgood : ∀ i, lambda ∉ Q i) (j : ι → ℕ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' u : O, rowCoprimeMask P S u * finiteSexticRow Q hgood j u *
      W (‖eisEmbedding u‖ ^ 2 / scale)) =
      ∑ E ∈ S.powerset,
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
          finiteSexticRow Q hgood j (primeSubsetGenerator P E) *
          ∑' z : O, finiteSexticRow Q hgood j z *
            W (‖eisEmbedding z‖ ^ 2 /
              (scale / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2)) := by
  exact tsum_masked_radial_dilations P hinj S (finiteSexticRow Q hgood j)
    (finiteSexticRow_mul Q hgood j) W scale
    (finiteSexticRow_radial_summable Q hcop hgood j W scale hscale)

theorem canonical_masked_radial_poisson
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (S : Finset α)
    (Q : ι → Ideal O) [∀ i, (Q i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime Q))
    (hgood : ∀ i, lambda ∉ Q i)
    (hchar : ∀ i, ringChar (O ⧸ Q i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus Q
    (∑' u : O, rowCoprimeMask P S u * finiteSexticRow Q hgood j u *
      W (‖eisEmbedding u‖ ^ 2 / scale)) =
      ∑ E ∈ S.powerset,
        let d := primeSubsetGenerator P E
        let reducedScale := scale / ‖eisEmbedding d‖ ^ 2
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
          finiteSexticRow Q hgood j d *
          ((reducedScale : ℂ) * canonicalNormalizedGauss Q hcop hgood j /
            (‖eisEmbedding c‖ : ℂ)) *
          ∑' h : O, star (finiteSexticRow Q hgood j h) *
            paperRadialFourier W
              (reducedScale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  dsimp only
  rw [canonical_masked_radial_dilations P hinj S Q hcop hgood j W scale hscale]
  apply Finset.sum_congr rfl
  intro E hE
  rw [canonical_radial_poisson_normalized Q hcop hgood hchar j hj0 hj6 W
    (scale / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2)
    (primeSubset_reducedScale_pos P E hscale)]
  ring

theorem canonical_masked_radial_poisson_collected
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (S : Finset α)
    (Q : ι → Ideal O) [∀ i, (Q i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime Q))
    (hgood : ∀ i, lambda ∉ Q i)
    (hchar : ∀ i, ringChar (O ⧸ Q i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus Q
    (∑' u : O, rowCoprimeMask P S u * finiteSexticRow Q hgood j u *
      W (‖eisEmbedding u‖ ^ 2 / scale)) =
      ((scale : ℂ) * canonicalNormalizedGauss Q hcop hgood j / (‖eisEmbedding c‖ : ℂ)) *
        ∑ E ∈ S.powerset,
          let d := primeSubsetGenerator P E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
            finiteSexticRow Q hgood j d / (‖eisEmbedding d‖ ^ 2 : ℝ)) *
            ∑' h : O, star (finiteSexticRow Q hgood j h) *
              paperRadialFourier W
                (scale * ‖eisEmbedding h‖ ^ 2 /
                  (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding c‖ ^ 2)) := by
  dsimp only
  rw [canonical_masked_radial_poisson P hinj S Q hcop hgood hchar j hj0 hj6 W scale hscale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only
  have harg (h : O) :
      scale / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 * ‖eisEmbedding h‖ ^ 2 /
          ‖eisEmbedding (finitePrimeModulus Q)‖ ^ 2 =
      scale * ‖eisEmbedding h‖ ^ 2 /
        (‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 *
          ‖eisEmbedding (finitePrimeModulus Q)‖ ^ 2) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [harg]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.ActiveConductor
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace ActualEisensteinCubic

section

open ConcreteTraceCRT EisensteinSchwartzPoisson

 theorem finiteSexticRow_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) (a : O) :
    finiteSexticRow P hgood j a = 1 := by
  simp [finiteSexticRow]

 theorem finitePrimeModulus_norm_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) : ‖eisEmbedding (finitePrimeModulus P)‖ = 1 := by
  have h := finitePrimeModulus_norm_sq P
  simp only [Finset.univ_eq_empty, Finset.prod_empty, map_one, Nat.cast_one] at h
  nlinarith [norm_nonneg (eisEmbedding (finitePrimeModulus P))]

 theorem canonicalGaussSum_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) :
    canonicalGaussSum P hcop hgood j = 1 := by
  let c := finitePrimeModulus P
  have hc : Ideal.span {c} = ⊤ := by
    simpa only [c, Finset.univ_eq_empty, Finset.prod_empty, Ideal.one_eq_top] using
      span_finitePrimeModulus P
  have hzero (r : O ⧸ Ideal.span {c}) : r = 0 := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [hc]; trivial)
  let : Subsingleton (O ⧸ Ideal.span {c}) := ⟨fun a b => (hzero a).trans (hzero b).symm⟩
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span (finitePrimeModulus_ne_zero P)
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  unfold canonicalGaussSum
  change (∑ r : O ⧸ Ideal.span {c}, _ ) = 1
  rw [Fintype.sum_subsingleton _ 0]
  simp [principalSexticRow, finiteSexticQuotientRow]

 theorem canonicalNormalizedGauss_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) :
    canonicalNormalizedGauss P hcop hgood j = 1 := by
  rw [canonicalNormalizedGauss, canonicalGaussSum_of_isEmpty,
    finitePrimeModulus_norm_of_isEmpty, Complex.ofReal_one, div_one]

end

open EisensteinSchwartzPoisson

theorem primeSubset_moebius_norm_sum
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P) (S : Finset ι) :
    (∑ E ∈ S.powerset, (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
      (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) =
      ∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i)) := by
  rw [Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro E hE
  rw [prime_product_moebius P hprime hinj E]
  simp only [Finset.prod_const_one, mul_one,  map_prod, Nat.cast_prod,
    Finset.prod_inv_distrib, div_eq_mul_inv, one_mul]

end ActualEisensteinCubic

open scoped BigOperators Classical SchwartzMap ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.CoefficientCancellation
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem norm_ideal_moebius_le_one (I : Ideal O) :
    ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖ ≤ 1 := by
  unfold UniqueFactorizationMonoid.moebius
  split_ifs <;> simp

end QuadraticInitialBound

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.RayExpansion
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical
namespace QuadraticDivisorSplit

theorem exists_unique_split (B C D : Ideal O) (hBC : IsCoprime B C)
    (hD : D ∣ B * C) :
    ∃! x : Ideal O × Ideal O, x.1 ∣ B ∧ x.2 ∣ C ∧ x.1 * x.2 = D := by
  obtain ⟨D₁, D₂, h₁, h₂, hprod⟩ := exists_dvd_and_dvd_of_dvd_mul hD
  refine ⟨(D₁, D₂), ⟨h₁, h₂, hprod.symm⟩, ?_⟩
  intro y hy
  apply Prod.ext
  · apply associated_iff_eq.mp
    apply associated_of_dvd_dvd
    · apply (hBC.mono hy.1 h₂).dvd_of_dvd_mul_right
      rw [← hprod, ← hy.2.2]
      exact dvd_mul_right _ _
    · apply (hBC.mono h₁ hy.2.1).dvd_of_dvd_mul_right
      rw [hy.2.2, hprod]
      exact dvd_mul_right _ _
  · apply associated_iff_eq.mp
    apply associated_of_dvd_dvd
    · apply (hBC.symm.mono hy.2.1 h₁).dvd_of_dvd_mul_left
      rw [← hprod, ← hy.2.2]
      exact dvd_mul_left _ _
    · apply (hBC.symm.mono h₂ hy.1).dvd_of_dvd_mul_left
      rw [hy.2.2, hprod]
      exact dvd_mul_left _ _

theorem split_product_injective (B C : Ideal O) (hBC : IsCoprime B C) :
    Function.Injective (fun x : {x : Ideal O × Ideal O // x.1 ∣ B ∧ x.2 ∣ C} =>
      x.val.1 * x.val.2) := by
  intro x y hxy
  have hD : x.val.1 * x.val.2 ∣ B * C := mul_dvd_mul x.property.1 x.property.2
  obtain ⟨z, hz, huniq⟩ := exists_unique_split B C (x.val.1 * x.val.2) hBC hD
  apply Subtype.ext
  exact (huniq x.val ⟨x.property.1, x.property.2, rfl⟩).trans
    (huniq y.val ⟨y.property.1, y.property.2, hxy.symm⟩).symm

open IdealMobiusDivisorSum

theorem divisors_coprime_product (B C : Ideal O) (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : IsCoprime B C) :
    idealDivisors (B * C) =
      ((idealDivisors B) ×ˢ (idealDivisors C)).image (fun x => x.1 * x.2) := by
  ext D
  rw [mem_idealDivisors (mul_ne_zero hB hC), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨x, hx, _⟩ := exists_unique_split B C D hBC hD
    exact ⟨x, Finset.mem_product.mpr
      ⟨(mem_idealDivisors hB).mpr hx.1, (mem_idealDivisors hC).mpr hx.2.1⟩, hx.2.2⟩
  · rintro ⟨x, hx, rfl⟩
    exact mul_dvd_mul ((mem_idealDivisors hB).mp (Finset.mem_product.mp hx).1)
      ((mem_idealDivisors hC).mp (Finset.mem_product.mp hx).2)

theorem sum_divisors_coprime_product (B C : Ideal O) (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : IsCoprime B C) (f : Ideal O → ℂ) :
    (∑ D ∈ idealDivisors (B * C), f D) =
      ∑ D₁ ∈ idealDivisors B, ∑ D₂ ∈ idealDivisors C, f (D₁ * D₂) := by
  rw [divisors_coprime_product B C hB hC hBC, Finset.sum_image]
  · exact Finset.sum_product _ _ _
  · intro x hx y hy hxy
    have hx' : x.1 ∣ B ∧ x.2 ∣ C :=
      ⟨(mem_idealDivisors hB).mp (Finset.mem_product.mp hx).1,
        (mem_idealDivisors hC).mp (Finset.mem_product.mp hx).2⟩
    have hy' : y.1 ∣ B ∧ y.2 ∣ C :=
      ⟨(mem_idealDivisors hB).mp (Finset.mem_product.mp hy).1,
        (mem_idealDivisors hC).mp (Finset.mem_product.mp hy).2⟩
    have he : (⟨x, hx'⟩ : {z : Ideal O × Ideal O // z.1 ∣ B ∧ z.2 ∣ C}) = ⟨y, hy'⟩ :=
      split_product_injective B C hBC hxy
    exact congrArg Subtype.val he

end QuadraticDivisorSplit

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.ReflectionBrackets
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap
namespace ActualEisensteinCubic
open ConcreteTraceCRT ConcretePrimeRowBridge ActualEisensteinCoordinates EisensteinSchwartzPoisson

theorem primeSubsetGenerator_norm_sq {ι : Type*} (P : ι → Ideal O) (E : Finset ι) :
    ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 = (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ)) (span_idealGenerator _)

theorem masked_principal_radial_poisson {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (V : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask P S z * V (‖eisEmbedding z‖ ^ 2 / M)) =
      (M : ℂ) * ∑ E ∈ S.powerset,
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
          (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) *
        ∑' h : O, paperRadialFourier V
          (M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)) := by
  let Q : Empty → Ideal O := Empty.elim
  let : ∀ i, (Q i).IsMaximal := fun i => nomatch i
  have hcop : Pairwise (Function.onFun IsCoprime Q) := by intro i; cases i
  have hg : ∀ i, lambda ∉ Q i := fun i => nomatch i
  have hc : ∀ i, ringChar (O ⧸ Q i) ≠ 2 := fun i => nomatch i
  have hj0 : ∀ i : Empty, (1 : ℕ) ≠ 0 := fun i => nomatch i
  have hj6 : ∀ i : Empty, (1 : ℕ) < 6 := fun i => nomatch i
  have hp := canonical_masked_radial_poisson_collected P hinj S Q hcop hg hc
    (fun _ => 1) hj0 hj6 V M hM
  simpa only [finiteSexticRow_of_isEmpty, canonicalNormalizedGauss_of_isEmpty,
    finitePrimeModulus_norm_of_isEmpty, Complex.ofReal_one, mul_one, div_one,
    star_one, one_mul, one_pow, primeSubsetGenerator_norm_sq, Complex.ofReal_natCast] using hp

theorem masked_principal_radial_poisson_zero_split {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (V : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask P S z * V (‖eisEmbedding z‖ ^ 2 / M)) =
      (M : ℂ) * paperRadialFourier V 0 *
        (∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i))) +
        maskedPrincipalRemainder P S V M := by
  have hp (E : Finset ι) : 0 < (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by
    rw [← primeSubsetGenerator_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E)))
  have hs (E : Finset ι) :
      (∑' h : O, paperRadialFourier V
        (M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ))) =
      paperRadialFourier V 0 +
        ∑' h : O, if h = 0 then 0 else paperRadialFourier V
          (M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)) := by
    have hsum := (paperRadialFourier_lattice_summable_norm V
      (M / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)) (div_pos hM (hp E))).of_norm
    have heq (h : O) : M / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) * ‖eisEmbedding h‖ ^ 2 =
        M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by ring
    simp_rw [heq] at hsum
    simpa only [map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div]
      using hsum.tsum_eq_add_tsum_ite 0
  have hprime : ∀ i, Prime (P i) := fun i => Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
  rw [masked_principal_radial_poisson P hinj S V M hM]
  simp_rw [hs, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, mul_add]
  rw [primeSubset_moebius_norm_sum P hprime hinj S]
  unfold maskedPrincipalRemainder
  ring

end ActualEisensteinCubic

open scoped BigOperators Classical

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reciprocity.RamifiedSymbol
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap
namespace QuadraticUnitInvariance
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates
open GaussGeneratorTransport QuadraticGaussRay EisensteinSchwartzPoisson
open PrimaryIdealUnitReindex CompletedGauss

theorem rowCoprimeMask_unit_mul {α : Type*} (R : α → Ideal O)
    (S : Finset α) (u : Oˣ) (z : O) :
    rowCoprimeMask R S (u.val * z) = rowCoprimeMask R S z := by
  simp only [rowCoprimeMask, Ideal.unit_mul_mem_iff_mem _ u.isUnit]

theorem rowCoprimeMask_norm_le_one {α : Type*} (R : α → Ideal O)
    (S : Finset α) (z : O) : ‖rowCoprimeMask R S z‖ ≤ 1 := by
  unfold rowCoprimeMask
  split_ifs <;> simp

end QuadraticUnitInvariance

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.PrimitiveRows
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap
namespace TruncatedPrincipalPoisson

section
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson

theorem radialSource_summable (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    Summable (fun z : O => if z = 0 then 0 else W (‖eisEmbedding z‖ ^ 2 / X)) := by
  have hs : Summable (fun z : O => W (‖eisEmbedding z‖ ^ 2 / X)) := by
    simpa only [scaledRadialTest_apply] using
      (actual_eisenstein_summable_norm (scaledRadialTest W X hX)).of_norm
  convert (preTransparency := .instances) hs.indicator {z : O | z ≠ 0} using 1
  ext z
  by_cases hz : z = 0 <;> simp [hz]

theorem radialSource_poisson (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    radialSource W X = (X : ℂ) * paperRadialFourier W 0 - W 0 +
      (X : ℂ) * radialDual W X := by
  let P : Empty → Ideal O := Empty.elim
  let : ∀ i, (P i).IsMaximal := fun i => nomatch i
  have hi : Function.Injective P := by intro i; cases i
  have hp := masked_principal_radial_poisson_zero_split P hi ∅ W X hX
  simp only [maskedPrincipalRemainder, Finset.prod_empty, Finset.powerset_empty,
    Finset.sum_singleton, UniqueFactorizationMonoid.moebius_one, map_one,
    Int.cast_one, Nat.cast_one, div_one, mul_one] at hp
  simp only [rowCoprimeMask, Finset.notMem_empty, false_and, exists_false,
    ite_false, one_mul] at hp
  have hs : Summable (fun z : O => W (‖eisEmbedding z‖ ^ 2 / X)) := by
    simpa only [scaledRadialTest_apply] using
      (actual_eisenstein_summable_norm (scaledRadialTest W X hX)).of_norm
  have hz := hs.tsum_eq_add_tsum_ite 0
  simp only [map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div] at hz
  change (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / X)) =
    (X : ℂ) * paperRadialFourier W 0 + (X : ℂ) * radialDual W X at hp
  change (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / X)) = W 0 + radialSource W X at hz
  linear_combination hp - hz

theorem subsetNorm_pos {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (E : Finset ι) :
    0 < subsetNorm P E := by
  rw [subsetNorm, ← primeSubsetGenerator_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E)))

theorem sum_small_add_large {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    (S : Finset ι) (Z : ℝ) (f : Finset ι → ℂ) :
    (∑ E ∈ smallDivisors P S Z, f E) + (∑ E ∈ largeDivisors P S Z, f E) =
      ∑ E ∈ S.powerset, f E := by
  simpa only [smallDivisors, largeDivisors, not_le] using
    Finset.sum_filter_add_sum_filter_not S.powerset (fun E => subsetNorm P E ≤ Z) f

theorem masked_radialSource_dilations {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    (∑' z : O, rowCoprimeMask P S z *
      (if z = 0 then 0 else W (‖eisEmbedding z‖ ^ 2 / X))) =
      ∑ E ∈ S.powerset, subsetMobius P E * radialSource W (X / subsetNorm P E) := by
  rw [tsum_rowCoprimeMask_dilations P hinj S _ (radialSource_summable W X hX)]
  apply Finset.sum_congr rfl
  intro E hE
  change subsetMobius P E * _ = _
  congr 1
  apply tsum_congr
  intro z
  rw [mul_eq_zero, or_iff_right (primeSubsetGenerator_ne_zero P E)]
  by_cases hz : z = 0
  · simp [hz]
  · rw [if_neg hz, if_neg hz, map_mul, norm_mul, mul_pow, primeSubsetGenerator_norm_sq]
    congr 1
    simp only [subsetNorm, div_div_eq_mul_div]
    ring

theorem masked_radialSource_truncated {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Z : ℝ) (hX : 0 < X) :
    (∑' z : O, rowCoprimeMask P S z *
      (if z = 0 then 0 else W (‖eisEmbedding z‖ ^ 2 / X))) =
      (X : ℂ) * paperRadialFourier W 0 *
        (∑ E ∈ smallDivisors P S Z, subsetMobius P E / (subsetNorm P E : ℂ)) -
      W 0 * (∑ E ∈ smallDivisors P S Z, subsetMobius P E) +
      (X : ℂ) * (∑ E ∈ smallDivisors P S Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)) +
      (∑ E ∈ largeDivisors P S Z, subsetMobius P E * radialSource W (X / subsetNorm P E)) := by
  rw [masked_radialSource_dilations P hinj S W X hX,
    ← sum_small_add_large P S Z]
  congr 1
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  rw [radialSource_poisson W _ (div_pos hX (subsetNorm_pos P E))]
  push_cast
  ring

theorem masked_radialSource_truncated_euler {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Z : ℝ) (hX : 0 < X) :
    (∑' z : O, rowCoprimeMask P S z *
      (if z = 0 then 0 else W (‖eisEmbedding z‖ ^ 2 / X))) =
      (X : ℂ) * paperRadialFourier W 0 *
        (∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i))) -
      (X : ℂ) * paperRadialFourier W 0 *
        (∑ E ∈ largeDivisors P S Z, subsetMobius P E / (subsetNorm P E : ℂ)) -
      W 0 * (∑ E ∈ smallDivisors P S Z, subsetMobius P E) +
      (X : ℂ) * (∑ E ∈ smallDivisors P S Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)) +
      (∑ E ∈ largeDivisors P S Z, subsetMobius P E * radialSource W (X / subsetNorm P E)) := by
  rw [masked_radialSource_truncated P hinj S W X Z hX]
  have hs := sum_small_add_large P S Z (fun E => subsetMobius P E / (subsetNorm P E : ℂ))
  have hprime : ∀ i, Prime (P i) := fun i => Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
  have he := primeSubset_moebius_norm_sum P hprime hinj S
  change (∑ E ∈ S.powerset, subsetMobius P E / (subsetNorm P E : ℂ)) = _ at he
  rw [he] at hs
  linear_combination (X : ℂ) * paperRadialFourier W 0 * hs

end

local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem radialDual_summable (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    Summable (fun h : O => if h = 0 then 0 else paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2)) := by
  have hs := (paperRadialFourier_lattice_summable_norm W X hX).of_norm
  convert (preTransparency := .instances) hs.indicator {z : O | z ≠ 0} using 1
  ext z
  by_cases hz : z = 0 <;> simp [hz]

theorem radialDual_near_add_far (W : 𝓢(ℝ, ℂ)) (X lengthScale : ℝ) (hX : 0 < X) :
    radialDual W X = dualNear W X lengthScale + dualFar W X lengthScale := by
  have hs := radialDual_summable W X hX
  have hn : Summable (fun h : O => if ‖eisEmbedding h‖ ^ 2 ≤ lengthScale then
      (if h = 0 then 0 else paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2)) else 0) := by
    exact hs.indicator {h : O | ‖eisEmbedding h‖ ^ 2 ≤ lengthScale}
  have hf : Summable (fun h : O => if lengthScale < ‖eisEmbedding h‖ ^ 2 then
      (if h = 0 then 0 else paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2)) else 0) := by
    exact hs.indicator {h : O | lengthScale < ‖eisEmbedding h‖ ^ 2}
  unfold radialDual dualNear dualFar
  rw [← hn.tsum_add hf]
  apply tsum_congr
  intro h
  by_cases hL : ‖eisEmbedding h‖ ^ 2 ≤ lengthScale <;> simp [hL, not_lt_of_ge, lt_of_not_ge]

theorem sum_small_add_middle {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    (S : Finset ι) (Y Z : ℝ) (hYZ : Y ≤ Z) (f : Finset ι → ℂ) :
    (∑ E ∈ smallDivisors P S Y, f E) + (∑ E ∈ middleDivisors P S Y Z, f E) =
      ∑ E ∈ smallDivisors P S Z, f E := by
  have hsmall : (smallDivisors P S Z).filter (fun E => subsetNorm P E ≤ Y) =
      smallDivisors P S Y := by
    ext E
    simp only [Finset.mem_filter, smallDivisors]
    constructor
    · rintro ⟨⟨hE, hEZ⟩, hEY⟩
      exact ⟨hE, hEY⟩
    · rintro ⟨hE, hEY⟩
      exact ⟨⟨hE, hEY.trans hYZ⟩, hEY⟩
  have hs := Finset.sum_filter_add_sum_filter_not (smallDivisors P S Z)
    (fun E => subsetNorm P E ≤ Y) f
  rw [hsmall] at hs
  simpa only [middleDivisors, not_le] using hs

theorem masked_radialSource_five_pieces {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y Z lengthScale : ℝ) (hX : 0 < X) (hYZ : Y ≤ Z) :
    (∑' z : O, rowCoprimeMask P S z *
      (if z = 0 then 0 else W (‖eisEmbedding z‖ ^ 2 / X))) =
      (X : ℂ) * paperRadialFourier W 0 *
        (∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i))) -
      (X : ℂ) * paperRadialFourier W 0 *
        (∑ E ∈ largeDivisors P S Z, subsetMobius P E / (subsetNorm P E : ℂ)) -
      W 0 * (∑ E ∈ smallDivisors P S Z, subsetMobius P E) +
      (X : ℂ) * (∑ E ∈ middleDivisors P S Y Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * dualNear W (X / subsetNorm P E) lengthScale) +
      (X : ℂ) * (∑ E ∈ smallDivisors P S Y,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)) +
      (X : ℂ) * (∑ E ∈ middleDivisors P S Y Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale) +
      (∑ E ∈ largeDivisors P S Z, subsetMobius P E * radialSource W (X / subsetNorm P E)) := by
  rw [masked_radialSource_truncated_euler P hinj S W X Z hX]
  have hs := sum_small_add_middle P S Y Z hYZ (fun E =>
    (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E))
  rw [← hs]
  have hm : (∑ E ∈ middleDivisors P S Y Z,
      (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)) =
      (∑ E ∈ middleDivisors P S Y Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * dualNear W (X / subsetNorm P E) lengthScale) +
      (∑ E ∈ middleDivisors P S Y Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro E hE
    rw [radialDual_near_add_far W _ lengthScale (div_pos hX (subsetNorm_pos P E)), mul_add]
  rw [hm]
  ring

end TruncatedPrincipalPoisson

namespace EisensteinSchwartzPoisson
open ConcreteTraceCRT

theorem radial_source_nonzero_lattice_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K : ℝ), 1 ≤ K →
        (∑' h : {h : O // h ≠ 0}, ‖W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + K) ^ A := by
  let s : Finset (ℕ × ℕ) := Finset.Iic (A + 2, 0)
  let C : ℝ := 2 ^ (A + 2) * (eisensteinCauchyMass + 1)
  have hC : 0 < C := by
    have hm := eisensteinCauchyMass_nonneg
    dsimp [C]
    positivity
  refine ⟨s, C, hC, ?_⟩
  intro W K hK
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let B : ℝ := 2 ^ (A + 2) * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (q : ℝ) (hq : 0 ≤ q) : (1 + q) ^ (A + 2) * ‖W q‖ ≤ B := by
    have hh := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (A + 2, 0)) (k := A + 2) (n := 0) le_rfl le_rfl W q
    simp only [norm_iteratedFDeriv_zero, Real.norm_of_nonneg hq] at hh
    change (1 + q) ^ (A + 2) * ‖W q‖ ≤ B at hh
    exact hh
  have hp (h : {h : O // h ≠ 0}) : ‖W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
      (B / (1 + K) ^ A) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := by
    have hq : K ≤ K * ‖eisEmbedding h.val‖ ^ 2 := by
      nlinarith [one_le_eisenstein_norm_sq h.val h.property]
    have hh := polynomial_tail_majorant A K K (‖eisEmbedding h.val‖ ^ 2) B
      ‖W (K * ‖eisEmbedding h.val‖ ^ 2)‖ hK0 hK0.le (sq_nonneg _) (norm_nonneg _) hq
      (hb _ (by positivity))
    simpa only [min_eq_left hK, one_pow, one_mul] using hh
  have hmajor := (eisenstein_cauchy_summable.subtype (fun h => h ≠ 0)).mul_left
    (B / (1 + K) ^ A)
  have hs : Summable (fun h : {h : O // h ≠ 0} => ‖W (K * ‖eisEmbedding h.val‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp hmajor
  calc
    _ ≤ ∑' h : {h : O // h ≠ 0},
        (B / (1 + K) ^ A) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ :=
      hs.tsum_le_tsum hp hmajor
    _ = (B / (1 + K) ^ A) * ∑' h : {h : O // h ≠ 0},
        ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := tsum_mul_left
    _ ≤ (B / (1 + K) ^ A) * eisensteinCauchyMass :=
      mul_le_mul_of_nonneg_left (eisensteinCauchyMass_subtype {h : O | h ≠ 0}) (by positivity)
    _ ≤ (B / (1 + K) ^ A) * (eisensteinCauchyMass + 1) := by
      gcongr
      linarith
    _ = _ := by dsimp [B, C]; ring

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap
namespace TruncatedPrincipalPoisson
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

private theorem zero_removed_tsum (f : O → ℂ) :
    (∑' h : O, if h = 0 then 0 else f h) = ∑' h : {h : O // h ≠ 0}, f h.val := by
  rw [← tsum_subtype_eq_of_support_subset (s := {h : O | h ≠ 0}) (by
    intro h hh hz
    subst h
    exact hh (by simp))]
  apply tsum_congr
  intro h
  simp only [if_neg h.property]

theorem radialSource_inverse_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K : ℝ), 1 ≤ K →
        ‖radialSource W K⁻¹‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + K) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := radial_source_nonzero_lattice_decay A
  refine ⟨s, C, hC, ?_⟩
  intro W K hK
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hs : Summable (fun h : O => W (K * ‖eisEmbedding h‖ ^ 2)) := by
    simpa only [scaledRadialTest_apply, div_inv_eq_mul, mul_comm] using
      (actual_eisenstein_summable_norm (scaledRadialTest W K⁻¹ (inv_pos.mpr hK0))).of_norm
  unfold radialSource
  rw [zero_removed_tsum]
  simp only [div_inv_eq_mul, mul_comm (‖eisEmbedding _‖ ^ 2) K]
  exact (norm_tsum_le_tsum_norm (hs.norm.subtype _)).trans (hb W K hK)

theorem radialDual_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K : ℝ), 1 ≤ K →
        ‖radialDual W K‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + K) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W K hK
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hs := paperRadialFourier_lattice_summable_norm W K hK0
  let f : {h : O // h ≠ 0} → {h : O // K ≤ K * ‖eisEmbedding h‖ ^ 2} :=
    fun h => ⟨h.val, by nlinarith [one_le_eisenstein_norm_sq h.val h.property]⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : {h : O // K ≤ K * ‖eisEmbedding h‖ ^ 2} => z.val) hab)
  have hi : (∑' h : {h : O // h ≠ 0}, ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
      ∑' h : {h : O // K ≤ K * ‖eisEmbedding h‖ ^ 2}, ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ :=
    (hs.subtype _).tsum_le_tsum_of_inj f hf (fun _ _ => norm_nonneg _) (fun _ => le_rfl) (hs.subtype _)
  have ht := hb W K K hK0 hK0.le
  simp only [min_eq_left hK, one_pow, one_mul] at ht
  unfold radialDual
  rw [zero_removed_tsum]
  exact (norm_tsum_le_tsum_norm (hs.subtype _)).trans (hi.trans ht)

theorem subsetMobius_norm_le_one {ι : Type*} (P : ι → Ideal O) (E : Finset ι) :
    ‖subsetMobius P E‖ ≤ 1 := QuadraticInitialBound.norm_ideal_moebius_le_one _

private theorem scale_tail_bound (A : ℕ) (B x Y X : ℝ)
    (hB : 0 ≤ B) (hx : 0 < x) (hxY : x ≤ Y) (hX : 0 < X) :
    (X / x) * (B / (1 + X / x) ^ (A + 1)) ≤ B * (Y / X) ^ A := by
  have hu : 0 < X / x := div_pos hX hx
  calc
    _ ≤ (X / x) * (B / (X / x) ^ (A + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hu.le
      exact div_le_div_of_nonneg_left hB (pow_pos hu _) (pow_le_pow_left₀ hu.le (by linarith) _)
    _ = B * (x / X) ^ A := by
      simp only [div_pow, pow_succ]
      field_simp

    _ ≤ B * (Y / X) ^ A := by gcongr

private theorem norm_sum_subsets_le {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (T : Finset (Finset ι)) (hT : T ⊆ S.powerset) (f : Finset ι → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hf : ∀ E ∈ T, ‖f E‖ ≤ B) :
    ‖∑ E ∈ T, f E‖ ≤ (2 : ℝ) ^ S.card * B := by
  calc
    _ ≤ ∑ E ∈ T, ‖f E‖ := norm_sum_le _ _
    _ ≤ ∑ E ∈ T, B := Finset.sum_le_sum hf
    _ = (T.card : ℝ) * B := by simp
    _ ≤ (2 : ℝ) ^ S.card * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      have hc := Finset.card_le_card hT
      rw [Finset.card_powerset] at hc
      exact_mod_cast hc

theorem small_divisor_dual_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y : ℝ), 0 < X → 0 ≤ Y → Y ≤ X →
        ‖(X : ℂ) * ∑ E ∈ smallDivisors P S Y,
          (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * (Y / X) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := radialDual_decay (A + 1)
  refine ⟨s, C, hC, ?_⟩
  intro ι _ P _ S W X Y hX hY hYX
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB : 0 ≤ B := by dsimp [B]; positivity
  rw [Finset.mul_sum]
  have hf (E : Finset ι) (hE : E ∈ smallDivisors P S Y) :
      ‖(X : ℂ) * ((subsetMobius P E / (subsetNorm P E : ℂ)) *
        radialDual W (X / subsetNorm P E))‖ ≤ B * (Y / X) ^ A := by
    have hn := subsetNorm_pos P E
    have hEY : subsetNorm P E ≤ Y := (Finset.mem_filter.mp hE).2
    have hscale : 1 ≤ X / subsetNorm P E := (le_div_iff₀ hn).mpr (by simpa using hEY.trans hYX)
    calc
      _ = (X / subsetNorm P E) * ‖subsetMobius P E‖ * ‖radialDual W (X / subsetNorm P E)‖ := by
        simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hX, abs_of_pos hn]
        ring
      _ ≤ (X / subsetNorm P E) * 1 * (B / (1 + X / subsetNorm P E) ^ (A + 1)) := by
        gcongr
        · exact subsetMobius_norm_le_one P E
        · exact hb W _ hscale
      _ ≤ B * (Y / X) ^ A := by
        simpa only [mul_one] using scale_tail_bound A B (subsetNorm P E) Y X hB hn hEY hX
  exact (norm_sum_subsets_le S _ (Finset.filter_subset _ _) _ _ (by positivity) hf).trans_eq (by ring)

theorem large_divisor_source_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Z : ℝ), 0 < X → X ≤ Z →
        ‖∑ E ∈ largeDivisors P S Z,
          subsetMobius P E * radialSource W (X / subsetNorm P E)‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            (1 + Z / X) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := radialSource_inverse_decay A
  refine ⟨s, C, hC, ?_⟩
  intro ι _ P _ S W X Z hX hXZ
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hZ : 0 < Z := hX.trans_le hXZ
  have hf (E : Finset ι) (hE : E ∈ largeDivisors P S Z) :
      ‖subsetMobius P E * radialSource W (X / subsetNorm P E)‖ ≤ B / (1 + Z / X) ^ A := by
    have hn := subsetNorm_pos P E
    have hEZ : Z < subsetNorm P E := (Finset.mem_filter.mp hE).2
    have hscale : 1 ≤ subsetNorm P E / X := (le_div_iff₀ hX).mpr (by simpa using hXZ.trans hEZ.le)
    have hh := hb W (subsetNorm P E / X) hscale
    rw [inv_div] at hh
    calc
      _ = ‖subsetMobius P E‖ * ‖radialSource W (X / subsetNorm P E)‖ := norm_mul _ _
      _ ≤ 1 * (B / (1 + subsetNorm P E / X) ^ A) :=
        mul_le_mul (subsetMobius_norm_le_one P E) hh (norm_nonneg _) (by norm_num)
      _ ≤ B / (1 + Z / X) ^ A := by
        simp only [one_mul]
        apply div_le_div_of_nonneg_left hB (by positivity)
        exact pow_le_pow_left₀ (by positivity) (by gcongr) A
  exact (norm_sum_subsets_le S _ (Finset.filter_subset _ _) _ _ (by positivity) hf).trans_eq (by ring)

end TruncatedPrincipalPoisson

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.PrincipalTruncation
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap
namespace TruncatedPrincipalPoisson

section
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson

theorem mem_rowNormDisk_floor {lengthScale : ℝ} (hL : 0 ≤ lengthScale) (z : O) :
    z ∈ rowNormDisk ⌊lengthScale⌋₊ ↔ z ≠ 0 ∧ ‖eisEmbedding z‖ ^ 2 ≤ lengthScale := by
  rw [mem_rowNormDisk]
  constructor
  · rintro ⟨hp, hN⟩
    refine ⟨?_, ?_⟩
    · intro hz
      subst z
      simp at hp
    · rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hL)
  · rintro ⟨hz, hN⟩
    have hp := sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hz))
    rw [eisEmbedding_norm_sq_eq_absNorm_span] at hp hN
    exact ⟨by exact_mod_cast hp, Nat.le_floor hN⟩

theorem dualNear_eq_finite (W : ℝ → ℂ) (X lengthScale : ℝ) (hL : 0 ≤ lengthScale) :
    dualNear W X lengthScale =
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2) := by
  unfold dualNear
  rw [tsum_eq_sum (s := rowNormDisk ⌊lengthScale⌋₊) (fun h hh => ?_)]
  · apply Finset.sum_congr rfl
    intro h hh
    have hd := (mem_rowNormDisk_floor hL h).mp hh
    simp only [if_pos hd.2, if_neg hd.1]
  · by_cases hz : h = 0
    · simp [hz]
    · have hn : ¬ ‖eisEmbedding h‖ ^ 2 ≤ lengthScale := fun hn => hh ((mem_rowNormDisk_floor hL h).mpr ⟨hz, hn⟩)
      simp only [if_neg hn]

theorem dualFar_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K lengthScale : ℝ), 0 < K → 0 ≤ lengthScale →
        ‖dualFar W K lengthScale‖ ≤ (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K) ^ 2 * (1 + K * lengthScale) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W K lengthScale hK hL
  have he : dualFar W K lengthScale =
      ∑' h : {h : O // lengthScale < ‖eisEmbedding h‖ ^ 2}, paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2) := by
    unfold dualFar
    rw [← tsum_subtype_eq_of_support_subset (s := {h : O | lengthScale < ‖eisEmbedding h‖ ^ 2}) (by
      intro h hh
      by_contra hn
      change ¬ lengthScale < ‖eisEmbedding h‖ ^ 2 at hn
      exact hh (by simp only [if_neg hn]))]
    apply tsum_congr
    intro h
    have hqh : lengthScale < ‖eisEmbedding h.val‖ ^ 2 := h.property
    have hz : h.val ≠ 0 := by
      intro hz
      have hp := hqh
      simp only [hz, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hp
      linarith
    simp only [if_pos hqh, if_neg hz]
  rw [he]
  have hs := paperRadialFourier_lattice_summable_norm W K hK
  let f : {h : O // lengthScale < ‖eisEmbedding h‖ ^ 2} →
      {h : O // K * lengthScale ≤ K * ‖eisEmbedding h‖ ^ 2} :=
    fun h => ⟨h.val, mul_le_mul_of_nonneg_left h.property.le hK.le⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : {h : O // K * lengthScale ≤ K * ‖eisEmbedding h‖ ^ 2} => z.val) hab)
  have hi : (∑' h : {h : O // lengthScale < ‖eisEmbedding h‖ ^ 2},
      ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
      ∑' h : {h : O // K * lengthScale ≤ K * ‖eisEmbedding h‖ ^ 2},
        ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ :=
    (hs.subtype _).tsum_le_tsum_of_inj f hf (fun _ _ => norm_nonneg _) (fun _ => le_rfl) (hs.subtype _)
  exact (norm_tsum_le_tsum_norm (hs.subtype _)).trans (hi.trans (hb W K (K * lengthScale) hK (mul_nonneg hK.le hL)))

end

section
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem middle_divisor_frequency_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y Z lengthScale : ℝ),
        0 < X → 0 < Y → Y ≤ Z → 0 ≤ lengthScale →
        ‖(X : ℂ) * ∑ E ∈ middleDivisors P S Y Z,
          (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale‖ ≤
          (2 : ℝ) ^ S.card * (X / Y) * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := dualFar_decay A
  refine ⟨s, C, hC, ?_⟩
  intro ι _ P _ S W X Y Z lengthScale hX hY hYZ hL
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let Q := (min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hZ : 0 < Z := hY.trans_le hYZ
  have hQ : 0 < Q := by dsimp [Q]; positivity
  rw [Finset.mul_sum]
  have hf (E : Finset ι) (hE : E ∈ middleDivisors P S Y Z) :
      ‖(X : ℂ) * ((subsetMobius P E / (subsetNorm P E : ℂ)) *
        dualFar W (X / subsetNorm P E) lengthScale)‖ ≤ (X / Y) * (B / Q) := by
    have hn := subsetNorm_pos P E
    have hEY : Y < subsetNorm P E := (Finset.mem_filter.mp hE).2
    have hEZ : subsetNorm P E ≤ Z := (Finset.mem_filter.mp (Finset.mem_filter.mp hE).1).2
    have hk : X / Z ≤ X / subsetNorm P E := div_le_div_of_nonneg_left hX.le hn hEZ
    have hden : Q ≤ (min 1 (X / subsetNorm P E)) ^ 2 *
        (1 + (X / subsetNorm P E) * lengthScale) ^ A := by
      dsimp [Q]
      have hmul : X * lengthScale / Z ≤ (X / subsetNorm P E) * lengthScale := by
        calc
          _ = (X / Z) * lengthScale := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hk hL
      apply mul_le_mul
      · exact pow_le_pow_left₀ (by positivity) (min_le_min_left _ hk) 2
      · exact pow_le_pow_left₀ (by positivity) (by linarith) A
      · positivity
      · positivity
    have hh : ‖dualFar W (X / subsetNorm P E) lengthScale‖ ≤ B / Q :=
      (hb W _ lengthScale (div_pos hX hn) hL).trans (div_le_div_of_nonneg_left hB hQ hden)
    calc
      _ = (X / subsetNorm P E) * ‖subsetMobius P E‖ * ‖dualFar W (X / subsetNorm P E) lengthScale‖ := by
        simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hX, abs_of_pos hn]
        ring
      _ ≤ (X / Y) * 1 * (B / Q) := by
        apply mul_le_mul
        · exact mul_le_mul (div_le_div_of_nonneg_left hX.le hY hEY.le)
            (subsetMobius_norm_le_one P E) (norm_nonneg _) (by positivity)
        · exact hh
        · exact norm_nonneg _
        · positivity
      _ = _ := by ring
  calc
    _ ≤ ∑ E ∈ middleDivisors P S Y Z,
        ‖(X : ℂ) * ((subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale)‖ := norm_sum_le _ _
    _ ≤ ∑ E ∈ middleDivisors P S Y Z, (X / Y) * (B / Q) := Finset.sum_le_sum hf
    _ = ((middleDivisors P S Y Z).card : ℝ) * ((X / Y) * (B / Q)) := by simp
    _ ≤ (2 : ℝ) ^ S.card * ((X / Y) * (B / Q)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hsub : middleDivisors P S Y Z ⊆ S.powerset :=
        (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
      have hc := Finset.card_le_card hsub
      rw [Finset.card_powerset] at hc
      exact_mod_cast hc
    _ = _ := by dsimp [B, Q]; ring

end

local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson

theorem truncationError_eq {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y Z lengthScale : ℝ) (hX : 0 < X) (hYZ : Y ≤ Z) (hL : 0 ≤ lengthScale) :
    truncationError P S W X Y Z lengthScale =
      (X : ℂ) * (∑ E ∈ smallDivisors P S Y,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)) +
      (X : ℂ) * (∑ E ∈ middleDivisors P S Y Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale) +
      (∑ E ∈ largeDivisors P S Z, subsetMobius P E * radialSource W (X / subsetNorm P E)) := by
  unfold truncationError principalTruncation middleTruncation
  rw [masked_radialSource_five_pieces P hinj S W X Y Z lengthScale hX hYZ]
  simp_rw [dualNear_eq_finite W _ lengthScale hL]
  ring

theorem truncationError_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (_hinj : Function.Injective P) (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y Z lengthScale : ℝ),
        0 < X → 0 < Y → Y ≤ X → X ≤ Z → 0 ≤ lengthScale →
        ‖truncationError P S W X Y Z lengthScale‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
            ((Y / X) ^ A + (1 / (1 + Z / X) ^ A) +
              (X / Y) / ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A)) := by
  obtain ⟨s₀, C₀, hC₀, h₀⟩ := small_divisor_dual_tail A
  obtain ⟨s₁, C₁, hC₁, h₁⟩ := large_divisor_source_tail A
  obtain ⟨s₂, C₂, hC₂, h₂⟩ := middle_divisor_frequency_tail A
  refine ⟨(s₀ ∪ s₁) ∪ s₂, C₀ + C₁ + C₂, by positivity, ?_⟩
  intro ι _ P _ hinj S W X Y Z lengthScale hX hY hYX hXZ hL
  let Q := ((s₀ ∪ s₁) ∪ s₂).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let C := C₀ + C₁ + C₂
  have hQ : 0 ≤ Q := apply_nonneg _ _
  have hc₀ : C₀ ≤ C := by dsimp [C]; linarith
  have hc₁ : C₁ ≤ C := by dsimp [C]; linarith
  have hc₂ : C₂ ≤ C := by dsimp [C]; linarith
  have hq₀ : s₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left.trans Finset.subset_union_left)) W
  have hq₁ : s₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_right.trans Finset.subset_union_left)) W
  have hq₂ : s₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) W
  have hz : 0 < Z := hX.trans_le hXZ
  let lo : ℂ := (X : ℂ) * ∑ E ∈ smallDivisors P S Y,
    (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)
  let mid : ℂ := (X : ℂ) * ∑ E ∈ middleDivisors P S Y Z,
    (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale
  let hi : ℂ := ∑ E ∈ largeDivisors P S Z,
    subsetMobius P E * radialSource W (X / subsetNorm P E)
  have hlo : ‖lo‖ ≤ (2 : ℝ) ^ S.card * (C * Q) * (Y / X) ^ A := by
    apply (h₀ P S W X Y hX hY.le hYX).trans
    gcongr
  have hhi : ‖hi‖ ≤ (2 : ℝ) ^ S.card * (C * Q) / (1 + Z / X) ^ A := by
    apply (h₁ P S W X Z hX hXZ).trans
    gcongr
  have hmid : ‖mid‖ ≤ (2 : ℝ) ^ S.card * (X / Y) * (C * Q) /
      ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A) := by
    apply (h₂ P S W X Y Z lengthScale hX hY (hYX.trans hXZ) hL).trans
    gcongr
  rw [truncationError_eq P hinj S W X Y Z lengthScale hX (hYX.trans hXZ) hL]
  change ‖lo + mid + hi‖ ≤ _
  calc
    _ ≤ ‖lo‖ + ‖mid‖ + ‖hi‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le lo mid) le_rfl)
    _ ≤ (2 : ℝ) ^ S.card * (C * Q) * (Y / X) ^ A +
        (2 : ℝ) ^ S.card * (X / Y) * (C * Q) / ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A) +
        (2 : ℝ) ^ S.card * (C * Q) / (1 + Z / X) ^ A := add_le_add (add_le_add hlo hmid) hhi
    _ = _ := by change _ = (2 : ℝ) ^ S.card * (C * Q) * _; ring

end TruncatedPrincipalPoisson

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.ConstantTermSupport
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

theorem singleton_rowCoprimeMask_eq_idealZeroMask (D : Ideal O) (z : O) :
    rowCoprimeMask (fun P : primePool {D} => P.val) Finset.univ z = idealZeroMask D z := by
  have he : (∃ P ∈ (Finset.univ : Finset (primePool {D})), z ∈ P.val) ↔
      ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors D, z ∈ P := by
    constructor
    · rintro ⟨P, _, hz⟩
      obtain ⟨I, hI, hP⟩ := mem_primePool_iff.mp P.property
      have hID : I = D := Finset.mem_singleton.mp hI
      exact ⟨P.val, hID ▸ hP, hz⟩
    · rintro ⟨P, hP, hz⟩
      have hp : P ∈ primePool {D} := mem_primePool_iff.mpr ⟨D, Finset.mem_singleton_self D, hP⟩
      exact ⟨⟨P, hp⟩, Finset.mem_univ _, hz⟩
  simp only [rowCoprimeMask, idealZeroMask, he]

theorem canonical_quadraticRow_star (D : Ideal O) (hD : Admissible D) (z : O) :
    star (quadraticRow D z) = quadraticRow D z := by
  let F : Finset (Ideal O) := {D}
  have hF : ∀ I ∈ F, Admissible I := by
    intro I hI
    have hID := Finset.mem_singleton.mp hI
    simpa only [hID] using hD
  rw [quadraticRow_eq_pool F hF D (Finset.mem_singleton_self D)]
  exact QuadraticInitialBound.quadraticRow_star _ _ _ _

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge
open EisensteinSchwartzPoisson GaussGeneratorTransport PrimaryIdealUnitReindex

theorem badPrime_injective : Function.Injective badPrime := by
  have hgood : lambda ∉ (Ideal.span {(2 : O)} : Ideal O) := by
    have hg := cubicTwoIdeal_good
    change lambda ∉ cubicTwoIdeal at hg
    simpa only [cubicTwoIdeal, Ideal.span_singleton_neg] using hg
  intro i j hij
  cases i <;> cases j
  · rfl
  · exfalso
    apply hgood
    have he : (Ideal.span {lambda} : Ideal O) = Ideal.span {(2 : O)} := hij
    rw [← he]
    exact Ideal.subset_span (by simp)
  · exfalso
    apply hgood
    have he : (Ideal.span {(2 : O)} : Ideal O) = Ideal.span {lambda} := hij
    rw [he]
    exact Ideal.subset_span (by simp)
  · rfl

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.UnrestrictedCharacters
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss

theorem unrestrictedPairCharacter_eq_primary (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (lengthScale : Ideal O) (hL : Supported lengthScale) :
    unrestrictedPairCharacter I J lengthScale =
      quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale) := by
  have hz := PrimaryIdealUnitReindex.primaryGenerator_ne_zero_of_good_factors lengthScale hL.1
    (fun P hP => (hL.2 P hP).1)
  have h := unrestrictedPairCharacter_span I J hI hJ hray (primaryGenerator lengthScale)
  rw [(primaryGenerator_spec lengthScale hz).1] at h
  exact h

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex GaussGeneratorTransport

theorem idealGenerator_norm_sq (lengthScale : Ideal O) :
    ‖eisEmbedding (idealGenerator lengthScale)‖ ^ 2 = (Ideal.absNorm lengthScale : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span, span_idealGenerator]

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open IdealMobiusDivisorSum

theorem goodSquarefreePart_admissible (I : Ideal O) : Admissible (goodSquarefreePart I) := by
  have hs : goodPrimeSupport I ⊆ IdealMobiusDivisorSum.primeSupport I := Finset.sdiff_subset
  refine ⟨support_product_ne_zero hs, squarefree_support_product hs, ?_⟩
  intro P hP
  change P ∈ UniqueFactorizationMonoid.normalizedFactors (∏ Q ∈ goodPrimeSupport I, Q) at hP
  rw [factors_support_product hs] at hP
  have hp : P ∈ goodPrimeSupport I := hP
  have hprime := support_prime (hs hp)
  let : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  exact (prime_good_iff_not_bad P).mpr (Finset.mem_sdiff.mp hp).2

theorem squarefree_bad_good_product (I : Ideal O) (hI : Squarefree I) :
    (∏ P ∈ badPrimeSupport I, P) * goodSquarefreePart I = I := by
  have hu : badPrimeSupport I ∪ goodPrimeSupport I = IdealMobiusDivisorSum.primeSupport I := by
    ext P
    simp only [badPrimeSupport, goodPrimeSupport, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hd : Disjoint (badPrimeSupport I) (goodPrimeSupport I) := by
    apply Finset.disjoint_left.mpr
    intro P hp hq
    exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_inter.mp hp).2
  rw [goodSquarefreePart, ← Finset.prod_union hd, hu]
  exact squarefree_support_product_self hI

theorem unrestrictedPairCharacter_squarefree_bad_split
    (I J B : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (hB : Squarefree B) :
    unrestrictedPairCharacter I J B =
      unrestrictedPairCharacter I J (∏ P ∈ badPrimeSupport B, P) *
        (quadraticRow I (primaryGenerator (goodSquarefreePart B)) *
          quadraticRow J (primaryGenerator (goodSquarefreePart B))) := by
  conv_lhs => rw [← squarefree_bad_good_product B hB]
  rw [unrestrictedPairCharacter_mul I J hI hJ hray,
    unrestrictedPairCharacter_eq_primary I J hI hJ hray _
      (admissible_supported (goodSquarefreePart_admissible B))]

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge

theorem fixedBadPrimes_card : fixedBadPrimes.card = 2 := by
  have hn : (Ideal.span {lambda} : Ideal O) ≠ Ideal.span {(2 : O)} := by
    intro h
    have hb : badPrime false = badPrime true := h
    have := badPrime_injective hb
    cases this
  simp [fixedBadPrimes, hn]

theorem fixedBadPrimes_powerset_card : fixedBadPrimes.powerset.card = 4 := by
  rw [Finset.card_powerset, fixedBadPrimes_card]
  norm_num

theorem goodSquarefreePart_injective_on_sector (I J : Ideal O) (hI : Squarefree I) (hJ : Squarefree J)
    (hs : badPrimeSector I = badPrimeSector J) (hg : goodSquarefreePart I = goodSquarefreePart J) : I = J := by
  have he : badPrimeSupport I = badPrimeSupport J := congrArg Subtype.val hs
  calc
    I = (∏ P ∈ badPrimeSupport I, P) * goodSquarefreePart I := (squarefree_bad_good_product I hI).symm
    _ = (∏ P ∈ badPrimeSupport J, P) * goodSquarefreePart J := by rw [he, hg]
    _ = J := squarefree_bad_good_product J hJ

theorem goodSquarefreePart_norm_le (I : Ideal O) (hI : Squarefree I) :
    Ideal.absNorm (goodSquarefreePart I) ≤ Ideal.absNorm I := by
  have hd : goodSquarefreePart I ∣ I := by
    exact ⟨∏ P ∈ badPrimeSupport I, P, (squarefree_bad_good_product I hI).symm.trans (mul_comm _ _)⟩
  apply Nat.le_of_dvd
  · exact Nat.pos_iff_ne_zero.mpr (fun hn => hI.ne_zero (Ideal.absNorm_eq_zero_iff.mp hn))
  · exact map_dvd Ideal.absNorm hd

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open QuadraticSquarefreeKernel UnrestrictedIdealReindex

end CanonicalQuadraticSieve

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.RamifiedNormWeights
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss

theorem idealZeroMask_mul (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) (z : O) :
    idealZeroMask (I * J) z = idealZeroMask I z * idealZeroMask J z := by
  have he : (∃ P ∈ UniqueFactorizationMonoid.normalizedFactors (I * J), z ∈ P) ↔
      (∃ P ∈ UniqueFactorizationMonoid.normalizedFactors I, z ∈ P) ∨
        (∃ P ∈ UniqueFactorizationMonoid.normalizedFactors J, z ∈ P) := by
    simp only [UniqueFactorizationMonoid.normalizedFactors_mul hI hJ, Multiset.mem_add,
      or_and_right, exists_or]
  unfold idealZeroMask
  simp only [he]
  by_cases h₁ : ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors I, z ∈ P <;>
    by_cases h₂ : ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors J, z ∈ P <;> simp [h₁, h₂]

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.TruncatedSecondTransfer
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex TruncatedPrincipalPoisson

theorem mem_squarefreeIdealRange {K : ℝ} {I : Ideal O} :
    I ∈ squarefreeIdealRange K ↔ Squarefree I ∧ (Ideal.absNorm I : ℝ) ≤ K := by
  rw [squarefreeIdealRange, Finset.mem_filter, mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hp, hN⟩, hs⟩
    refine ⟨hs, ?_⟩
    have hK : 0 ≤ K := by
      by_contra hn
      have hz : ⌊K⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hK)
  · rintro ⟨hs, hN⟩
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (fun h => hs.ne_zero (Ideal.absNorm_eq_zero_iff.mp h)),
      Nat.le_floor hN⟩, hs⟩

end CanonicalQuadraticSieve

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Fourier.LogDensity
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open IdealMobiusDivisorSum

theorem squarefree_divisor_sum_eq_support (G : Ideal O) (hG : Squarefree G) (f : Ideal O → ℂ) :
    (∑ D ∈ idealDivisors G, f D) =
      ∑ S ∈ (IdealMobiusDivisorSum.primeSupport G).powerset, f (∏ P ∈ S, P) := by
  have hfilter : (idealDivisors G).filter Squarefree = idealDivisors G := by
    apply Finset.filter_eq_self.mpr
    intro D hD
    exact hG.squarefree_of_dvd ((mem_idealDivisors hG.ne_zero).mp hD)
  rw [← hfilter, squarefree_divisors_eq_image G hG.ne_zero, Finset.sum_image]
  intro S hS T hT hST
  exact support_product_injective (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) hST

end

open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss IdealMobiusDivisorSum

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FirstCoreCutoff
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

open IdealCoprimeSieveOperator DivisorBlockCauchy

variable {n p : Type*} [Fintype n] [Fintype p]

theorem divisorEnergyFactor_nonneg (ε : ℝ) (hε : 0 < ε) (N : ℝ) (a : n → ℂ) (b : p → ℂ) :
    0 ≤ divisorEnergyFactor ε hε N a b := by
  have hs := (supportConstant_pos ε hε).le
  have hd := (divisorConstant_pos ε hε).le
  unfold divisorEnergyFactor
  positivity

theorem divisorBlockCost_sqrt (ε : ℝ) (hε : 0 < ε) (D₁ D₂ M N : ℝ)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (a : n → ℂ) (b : p → ℂ) :
    Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) =
      divisorEnergyFactor ε hε N a b *
        Real.sqrt (D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂)) := by
  have hA := sieveNorm_nonneg M (N / D₁)
  have hB := sieveNorm_nonneg M (N / D₂)
  have hp : 0 ≤ D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂) := by positivity
  have ha : 0 ≤ ∑ j, ‖a j‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb : 0 ≤ ∑ k, ‖b k‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc : 0 ≤ divisorBlockCost ε hε D₁ D₂ M N a b := by
    unfold divisorBlockCost
    positivity
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (divisorEnergyFactor_nonneg ε hε N a b) (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt hc]
  simp only [divisorEnergyFactor, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hp]
  unfold divisorBlockCost
  ring

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.SpatialDerivatives
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem principal_middle_prefactor_bound (M B b D₁ d D₂ e : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : B / 2 ≤ b)
    (hD₁ : 0 < D₁) (hd : D₁ ≤ d) (hD₂ : 0 < D₂) (he : D₂ ≤ e) :
    Real.sqrt (M / b) / (d * e) ≤ 2 * Real.sqrt (M / B) / (D₁ * D₂) := by
  have hb0 : 0 < b := by linarith
  have hd0 : 0 < d := hD₁.trans_le hd
  have he0 : 0 < e := hD₂.trans_le he
  have hq : M / b ≤ 4 * (M / B) := by
    calc
      _ ≤ (4 * M) / B := (div_le_div_iff₀ hb0 hB).mpr (by nlinarith [mul_nonneg hM.le (show 0 ≤ 4 * b - B by linarith)])
      _ = _ := by ring
  have hs : Real.sqrt (M / b) ≤ 2 * Real.sqrt (M / B) := by
    have hh := Real.sqrt_le_sqrt hq
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at hh
    have hs4 : Real.sqrt (4 : ℝ) = 2 := by
      simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)
    rw [hs4] at hh
    exact hh
  calc
    _ ≤ (2 * Real.sqrt (M / B)) / (d * e) := div_le_div_of_nonneg_right hs (mul_pos hd0 he0).le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (mul_pos hD₁ hD₂)
      (mul_le_mul hd he hD₂.le hd0.le)

theorem principal_middle_prefactor_sum {m : Type*} [Fintype m]
    (S T : Finset (Ideal O)) (rows : m → Ideal O) (f : S → T → m → ℝ)
    (hf : ∀ D E i, 0 ≤ f D E i) (M B D₁ D₂ : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hD₁ : 0 < D₁) (hD₂ : 0 < D₂)
    (hrows : ∀ i, B / 2 ≤ (Ideal.absNorm (rows i) : ℝ))
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ)) (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ)) :
    (∑ D : S, ∑ E : T, ∑ i,
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) * f D E i) ≤
      (2 * Real.sqrt (M / B) / (D₁ * D₂)) * ∑ D : S, ∑ E : T, ∑ i, f D E i := by
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro D _
  apply Finset.sum_le_sum
  intro E _
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (hf D E i)
  exact principal_middle_prefactor_bound M B _ D₁ _ D₂ _ hM hB (hrows i) hD₁
    (hS D.val D.property) hD₂ (hT E.val E.property)

theorem dual_principal_prefactor_identity (M F b i j : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hb : 0 < b) (hi : 0 < i) (hj : 0 < j) :
    (M / (Real.sqrt (i * j) * F)) * Real.sqrt (F * i * j / (M * b)) =
      Real.sqrt ((M / F) / b) := by
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  simp only [mul_pow, div_pow, Real.sq_sqrt (show 0 ≤ i * j by positivity),
    Real.sq_sqrt (show 0 ≤ F * i * j / (M * b) by positivity),
    Real.sq_sqrt (show 0 ≤ (M / F) / b by positivity)]
  field_simp

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
variable (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
  (a : n → ℂ) (b : p → ℂ) (h : O) (hh : h ≠ 0)

include hD₁ hD₂ hB hN hM hS hT hr hl hri hrows hh

end CanonicalQuadraticSieve

open Filter
open scoped BigOperators Classical Topology

open Filter
open scoped BigOperators Classical Topology

open Filter
open scoped BigOperators Classical Topology

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SmoothSummands
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic IdealMobiusDivisorSum IdealCoprimeSieveOperator

lemma divisorPool_filter (S : Finset (Ideal O)) (B : Ideal O) (hB : B ≠ 0)
    (hS : ∀ D, D ∣ B → D ∈ S) :
    S.filter (fun D => D ∣ B) = idealDivisors B := by
  ext D
  simp only [Finset.mem_filter, mem_idealDivisors hB]
  exact ⟨And.right, fun h => ⟨hS D h,h⟩⟩

lemma divisor_product_delta (S T : Finset (Ideal O)) (B C d : Ideal O)
    (hB : B ≠ 0) (hC : C ≠ 0) (hBC : IsCoprime B C)
    (hS : ∀ D, D ∣ B → D ∈ S) (hT : ∀ E, E ∣ C → E ∈ T)
    (f : Ideal O → ℂ) :
    (∑ D ∈ S, if D ∣ B then
      ∑ E ∈ T, if E ∣ C then (if D*E=d then f (D*E) else 0) else 0 else 0) =
      if d ∣ B*C then f d else 0 := by
  have hs := QuadraticDivisorSplit.sum_divisors_coprime_product B C hB hC hBC
    (fun q => if q=d then f q else 0)
  have hleft : (∑ q ∈ idealDivisors (B*C), if q=d then f q else 0) =
      if d ∣ B*C then f d else 0 := by
    simp [mem_idealDivisors (mul_ne_zero hB hC)]
  rw [hleft] at hs
  rw [← divisorPool_filter S B hB hS, ← divisorPool_filter T C hC hT] at hs
  simpa only [Finset.sum_filter] using hs.symm

private lemma four_sums_exchange {α β γ deltaLoss : Type*}
    (S : Finset α) (T : Finset β) (U : Finset γ) (V : Finset deltaLoss)
    (f : α → β → γ → deltaLoss → ℂ) :
    (∑ a ∈ S, ∑ b ∈ T, ∑ c ∈ U, ∑ d ∈ V, f a b c d) =
      ∑ c ∈ U, ∑ d ∈ V, ∑ a ∈ S, ∑ b ∈ T, f a b c d := by
  have h : (∑ ab ∈ S ×ˢ T, ∑ cd ∈ U ×ˢ V, f ab.1 ab.2 cd.1 cd.2) =
      ∑ cd ∈ U ×ˢ V, ∑ ab ∈ S ×ˢ T, f ab.1 ab.2 cd.1 cd.2 := Finset.sum_comm
  simpa only [Finset.sum_product] using h

private lemma three_sums_exchange {α β γ : Type*}
    (S : Finset α) (T : Finset β) (U : Finset γ) (f : α → β → γ → ℝ) :
    (∑ a ∈ S, ∑ b ∈ T, ∑ c ∈ U, f a b c) =
      ∑ b ∈ T, ∑ c ∈ U, ∑ a ∈ S, f a b c := by
  have h : (∑ a ∈ S, ∑ bc ∈ T ×ˢ U, f a bc.1 bc.2) =
      ∑ bc ∈ T ×ˢ U, ∑ a ∈ S, f a bc.1 bc.2 := Finset.sum_comm
  simpa only [Finset.sum_product] using h

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalTerm_product_divisor (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (d : Ideal O) (i : m) (j : n) (k : p)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T)
    (F : Ideal O → m → n → p → ℂ) :
    (∑ D ∈ S, ∑ E ∈ T, if D*E=d then
      originalTerm rows left right a b D E i j k * F (D*E) i j k else 0) =
    (if d ∣ left j*right k then
      originalTerm rows left right a b 1 1 i j k * F d i j k else 0) := by
  by_cases hc : IsCoprime (left j) (right k)
  · have hd := divisor_product_delta S T (left j) (right k) d (hleft j) (hright k) hc
      (hS j) (hT k) (fun q =>
        star (quadraticRow (left j) (CompletedGauss.primaryGenerator (rows i)) * a j) *
          (quadraticRow (right k) (CompletedGauss.primaryGenerator (rows i)) * b k) * F q i j k)
    calc
      _ = (∑ D ∈ S, if D ∣ left j then ∑ E ∈ T, if E ∣ right k then
          (if D*E=d then
            star (quadraticRow (left j) (CompletedGauss.primaryGenerator (rows i)) * a j) *
              (quadraticRow (right k) (CompletedGauss.primaryGenerator (rows i)) * b k) * F (D*E) i j k
          else 0) else 0 else 0) := by
        apply Finset.sum_congr rfl
        intro D hD
        by_cases hd : D ∣ left j
        · simp only [if_pos hd]
          apply Finset.sum_congr rfl
          intro E hE
          by_cases he : E ∣ right k <;> by_cases hde : D*E=d <;>
            simp [originalTerm,hc,hd,he,hde]
        · simp [originalTerm,hc,hd]
      _ = _ := by simpa [originalTerm,hc] using hd
  · simp [originalTerm,hc]

omit [Fintype m] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalColumnSum_product_divisor (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (d : Ideal O) (i : m)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T)
    (F : Ideal O → m → n → p → ℂ) :
    (∑ j, ∑ k, if d ∣ left j*right k then
      originalTerm rows left right a b 1 1 i j k * F d i j k else 0) =
    ∑ D ∈ S, ∑ E ∈ T, if D*E=d then
      (∑ j, ∑ k, originalTerm rows left right a b D E i j k * F (D*E) i j k) else 0 := by
  calc
    _ = ∑ j, ∑ k, ∑ D ∈ S, ∑ E ∈ T, if D*E=d then
        originalTerm rows left right a b D E i j k * F (D*E) i j k else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      exact (originalTerm_product_divisor S T rows left right a b d i j k hleft hright hS hT F).symm
    _ = ∑ D ∈ S, ∑ E ∈ T, ∑ j, ∑ k, if D*E=d then
        originalTerm rows left right a b D E i j k * F (D*E) i j k else 0 :=
      four_sums_exchange Finset.univ Finset.univ S T _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro E hE
      by_cases h : D*E=d <;> simp [h]

omit [Fintype m] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalColumnSum_divisor_rectangles (K S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (i : m)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T)
    (P : Ideal O → m → Prop) [DecidablePred (fun d => P d i)]
    (F : Ideal O → m → n → p → ℂ) :
    (∑ d ∈ K, if P d i then ‖∑ j, ∑ k, if d ∣ left j*right k then
      originalTerm rows left right a b 1 1 i j k * F d i j k else 0‖ else 0) ≤
    ∑ D ∈ S, ∑ E ∈ T, if D*E ∈ K then if P (D*E) i then
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * F (D*E) i j k‖ else 0 else 0 := by
  let B := fun D E => ∑ j, ∑ k, originalTerm rows left right a b D E i j k * F (D*E) i j k
  have hpoint (d : Ideal O) :
      (if P d i then ‖∑ j, ∑ k, if d ∣ left j*right k then
        originalTerm rows left right a b 1 1 i j k * F d i j k else 0‖ else 0) ≤
      ∑ D ∈ S, ∑ E ∈ T, if D*E=d ∧ P d i then ‖B D E‖ else 0 := by
    by_cases hp : P d i
    · simp only [hp, and_true]
      rw [originalColumnSum_product_divisor S T rows left right a b d i hleft hright hS hT F]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro D hD
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro E hE
      by_cases h : D*E=d <;> simp [h,B]
    · simp [hp]
  calc
    _ ≤ ∑ d ∈ K, ∑ D ∈ S, ∑ E ∈ T, if D*E=d ∧ P d i then ‖B D E‖ else 0 :=
      Finset.sum_le_sum (fun d hd => hpoint d)
    _ = ∑ D ∈ S, ∑ E ∈ T, ∑ d ∈ K, if D*E=d ∧ P d i then ‖B D E‖ else 0 :=
      three_sums_exchange K S T _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro E hE
      have heq (d : Ideal O) : (if D*E=d ∧ P d i then ‖B D E‖ else 0) =
          if d=D*E then (if P (D*E) i then ‖B D E‖ else 0) else 0 := by
        by_cases h : d=D*E
        · subst d
          simp
        · simp [h,Ne.symm h]
      simp_rw [heq]
      simp only [Finset.sum_ite_eq', B]

end

open ActualEisensteinCubic

lemma divisorDyadicLabel_bounds (N : ℝ) (D : Ideal O)
    (hD : 1 ≤ (Ideal.absNorm D : ℝ)) (hDN : (Ideal.absNorm D : ℝ) ≤ N) :
    (2 : ℝ)^(divisorDyadicLabel N D).val/2 < (Ideal.absNorm D : ℝ) ∧
      (Ideal.absNorm D : ℝ) ≤ (2 : ℝ)^(divisorDyadicLabel N D).val := by
  unfold divisorDyadicLabel
  rw [dif_pos ⟨hD,hDN⟩]
  exact (positive_ideal_dyadic_exists N D hD hDN).choose_spec.2

lemma divisorDyadicScale_ge_one (j : ℕ) : 1 ≤ divisorDyadicScale j := le_max_left _ _

theorem divisorDyadicBin_bounds (S : Finset (Ideal O)) (N : ℝ)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N)
    (j : Fin (columnDyadicLength N+1)) (D : Ideal O) (hD : D ∈ divisorDyadicBin S N j) :
    divisorDyadicScale j.val ≤ (Ideal.absNorm D : ℝ) ∧
      (Ideal.absNorm D : ℝ) ≤ 2 * divisorDyadicScale j.val := by
  obtain ⟨hDS,hj⟩ := Finset.mem_filter.mp hD
  have hd := hS D hDS
  have hb := divisorDyadicLabel_bounds N D hd.1 hd.2
  rw [hj] at hb
  refine ⟨max_le hd.1 hb.1.le, ?_⟩
  have hm : (2 : ℝ)^j.val/2 ≤ divisorDyadicScale j.val := le_max_right _ _
  linarith [hb.2]

theorem divisorDyadicBin_scale_le (S : Finset (Ideal O)) (N : ℝ)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N)
    (j : Fin (columnDyadicLength N+1)) (hj : (divisorDyadicBin S N j).Nonempty) :
    divisorDyadicScale j.val ≤ N := by
  obtain ⟨D,hD⟩ := hj
  exact (divisorDyadicBin_bounds S N hS j D hD).1.trans (hS D (Finset.mem_filter.mp hD).1).2

theorem sum_divisorDyadicBins {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal O)) (N : ℝ) (f : Ideal O → A) :
    (∑ D ∈ S, f D) = ∑ j : Fin (columnDyadicLength N+1), ∑ D ∈ divisorDyadicBin S N j, f D := by
  simp only [divisorDyadicBin,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  simp

theorem sum_divisorDyadicRectangles {A : Type*} [AddCommMonoid A]
    (S T : Finset (Ideal O)) (N : ℝ) (f : Ideal O → Ideal O → A) :
    (∑ D ∈ S, ∑ E ∈ T, f D E) =
      ∑ j : Fin (columnDyadicLength N+1), ∑ k : Fin (columnDyadicLength N+1),
        ∑ D ∈ divisorDyadicBin S N j, ∑ E ∈ divisorDyadicBin T N k, f D E := by
  calc
    _ = ∑ j : Fin (columnDyadicLength N+1), ∑ D ∈ divisorDyadicBin S N j,
        ∑ E ∈ T, f D E := sum_divisorDyadicBins S N _
    _ = ∑ j : Fin (columnDyadicLength N+1), ∑ D ∈ divisorDyadicBin S N j,
        ∑ k : Fin (columnDyadicLength N+1), ∑ E ∈ divisorDyadicBin T N k, f D E := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro D hD
      exact sum_divisorDyadicBins T N (f D)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm

theorem mem_columnDivisorPool_of_dvd {n : Type*} [Fintype n]
    (left : n → Ideal O) (hleft : ∀ j, left j ≠ 0) (j : n) (D : Ideal O)
    (hD : D ∣ left j) : D ∈ columnDivisorPool left := by
  apply Finset.mem_biUnion.mpr
  exact ⟨j,Finset.mem_univ j,(IdealMobiusDivisorSum.mem_idealDivisors (hleft j)).mpr hD⟩

theorem columnDivisorPool_norm_bounds {n : Type*} [Fintype n]
    (left : n → Ideal O) (hleft : ∀ j, left j ≠ 0) (N : ℝ)
    (hN : ∀ j, (Ideal.absNorm (left j) : ℝ) ≤ N)
    (D : Ideal O) (hD : D ∈ columnDivisorPool left) :
    1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N := by
  obtain ⟨j,hj,hDj⟩ := Finset.mem_biUnion.mp hD
  have hd := (IdealMobiusDivisorSum.mem_idealDivisors (hleft j)).mp hDj
  have hDz : D ≠ 0 := by
    intro hz
    rw [hz,zero_dvd_iff] at hd
    exact hleft j hd
  have hDN : Ideal.absNorm D ≤ Ideal.absNorm (left j) :=
    Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (fun h => hleft j (Ideal.absNorm_eq_zero_iff.mp h)))
      (map_dvd Ideal.absNorm hd)
  refine ⟨?_,(Nat.cast_le.mpr hDN).trans (hN j)⟩
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hDz (Ideal.absNorm_eq_zero_iff.mp h))

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.LatticeEnvelopes
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap

namespace EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT

theorem nonzeroLatticeEnvelopeConstant_nonneg :
    0 ≤ nonzeroLatticeEnvelopeConstant := by
  have := eisensteinCauchyMass_nonneg
  unfold nonzeroLatticeEnvelopeConstant
  positivity

theorem scaled_cauchy_nonzero_mass (t : ℝ) (ht : 0 < t) :
    t * (∑' h : {h : O // h ≠ 0},
      ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) ≤
        nonzeroLatticeEnvelopeConstant := by
  let F : ℝ → ℂ := fun x => (((1 + x) ^ 2)⁻¹ : ℝ)
  have hF (x : ℝ) (hx : 0 ≤ x) : (1 + x) ^ 2 * ‖F x‖ ≤ 1 := by
    dsimp only [F]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [mul_inv_cancel₀ (by positivity : (1 + x) ^ 2 ≠ 0)]
  have hh := lattice_profile_nonzero_scaled_bound F 1 (by norm_num) hF t ht
  change t * (∑' h : {h : O // h ≠ 0}, ‖F (t * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
    nonzeroLatticeEnvelopeConstant * 1 at hh
  simpa only [F, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ ((1 + t * ‖eisEmbedding _‖ ^ 2) ^ 2)⁻¹ by positivity),
    mul_one] using hh

theorem nonzero_lattice_envelope_sum
    (t C : ℝ) (ht : 0 < t) (hC : 0 ≤ C)
    (f : {h : O // h ≠ 0} → ℝ) (hf : ∀ h, 0 ≤ f h)
    (hbound : ∀ h, (1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 * f h ≤ C) :
    Summable f ∧ t * (∑' h, f h) ≤ nonzeroLatticeEnvelopeConstant * C := by
  have hp (h : {h : O // h ≠ 0}) :
      f h ≤ C * ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using hbound h
  have hs := (scaled_eisenstein_cauchy_summable t ht).subtype (fun h : O => h ≠ 0)
  have hfs : Summable f := Summable.of_nonneg_of_le hf hp (hs.mul_left C)
  refine ⟨hfs, ?_⟩
  have hh := hfs.tsum_le_tsum hp (hs.mul_left C)
  rw [tsum_mul_left] at hh
  calc
    _ ≤ t * (C * ∑' h : {h : O // h ≠ 0},
        ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hh ht.le
    _ = C * (t * ∑' h : {h : O // h ≠ 0},
        ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) := by ring
    _ ≤ C * nonzeroLatticeEnvelopeConstant :=
      mul_le_mul_of_nonneg_left (scaled_cauchy_nonzero_mass t ht) hC
    _ = _ := mul_comm _ _

end EisensteinSchwartzPoisson

namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem dualMiddleDecayConstant_nonneg (W : 𝓢(ℝ, ℂ)) :
    0 ≤ dualMiddleDecayConstant W :=
  (actual_dual_middle_radial_block_bound.{0, 0, 0} W 2).choose_spec.1

theorem divisorBlockCost_mono_coefficients
    {n p : Type*} [Fintype n] [Fintype p]
    (ε : ℝ) (hε : 0 < ε) (D₁ D₂ B N : ℝ) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (a a₀ : n → ℂ) (b b₀ : p → ℂ)
    (ha : ∀ j, ‖a j‖ ≤ ‖a₀ j‖) (hb : ∀ k, ‖b k‖ ≤ ‖b₀ k‖) :
    divisorBlockCost ε hε D₁ D₂ B N a b ≤ divisorBlockCost ε hε D₁ D₂ B N a₀ b₀ := by
  have hA := sieveNorm_nonneg B (N / D₁)
  have hB := sieveNorm_nonneg B (N / D₂)
  unfold divisorBlockCost
  gcongr
  · exact ha _
  · exact hb _

section
variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleAt_nonneg (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (h : O) :
    0 ≤ dualMiddleAt W S T rows left right a b M F h := by
  unfold dualMiddleAt
  positivity

variable (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
  (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
  (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)

include hD₁ hD₂ hB hN hM hS hT hr hl hri hrows ha hb

end

theorem dual_middle_scale_identity (M F B N : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 < B) (hN : 0 < N) :
    Real.sqrt ((M / F) / B) = (M / (F * N)) * (N * Real.sqrt (F / (M * B))) := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  simp only [mul_pow, div_pow, Real.sq_sqrt (show 0 ≤ (M / F) / B by positivity),
    Real.sq_sqrt (show 0 ≤ F / (M * B) by positivity)]
  field_simp

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem actual_dual_middle_all_frequencies
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M F : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hM : 0 < M) (hF : 0 < F)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ))
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N) :
    Summable (fun h : {h : O // h ≠ 0} =>
      dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val) ≤
        (2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) * (M / (F * N)) *
          Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a₀ b₀) := by
  let t := (N * Real.sqrt (F / (M * B))) / (D₁ * D₂)
  let r := M / (F * N)
  have ht : 0 < t := by dsimp only [t]; positivity
  have hr0 : 0 < r := by dsimp only [r]; positivity
  let C := dualMiddleDecayConstant W * Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a₀ b₀)
  have hC : 0 ≤ C := mul_nonneg (dualMiddleDecayConstant_nonneg W) (Real.sqrt_nonneg _)
  have hpoint (h : {h : O // h ≠ 0}) :
      (1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 *
        dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val ≤ (2 * t * r) * C := by
    have hk := (actual_dual_middle_radial_block_bound.{0, 0, 0} W 2).choose_spec.2 ε hε S T D₁ D₂ B N M F
      hD₁ hD₂ hB hN hM hF hS hT rows left right hr hl hri hrows hleft hright (a h.val) (b h.val) h.val h.property
    change _ ≤ dualMiddleDecayConstant W *
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N (a h.val) (b h.val)) at hk
    have hcost := divisorBlockCost_mono_coefficients ε hε D₁ D₂ B N
      (by linarith) (by linarith) (a h.val) a₀ (b h.val) b₀ (ha h.val) (hb h.val)
    have hk' := hk.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcost)
      (dualMiddleDecayConstant_nonneg W))
    have hp := principal_middle_prefactor_sum S T rows
      (fun D E i => ‖∑ j, ∑ k, originalTerm rows left right (a h.val) (b h.val) D.val E.val i j k *
        paperRadialFourier W (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h.val‖ ^ 2 /
            ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖)
      (fun _ _ _ => norm_nonneg _) (M / F) B D₁ D₂ (div_pos hM hF) (by linarith) (by linarith) (by linarith)
      (fun i => (hrows i).2.1) (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)
    have harg : N * Real.sqrt (F / (M * B)) * ‖eisEmbedding h.val‖ ^ 2 / (D₁ * D₂) =
        t * ‖eisEmbedding h.val‖ ^ 2 := by dsimp only [t]; ring
    rw [harg] at hk'
    have hpre : 2 * Real.sqrt ((M / F) / B) / (D₁ * D₂) = 2 * t * r := by
      rw [dual_middle_scale_identity M F B N hM hF (by linarith) (by linarith)]
      dsimp only [t, r]
      ring
    rw [hpre] at hp
    change dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val ≤ _ at hp
    calc
      _ ≤ (1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 * ((2 * t * r) * _) :=
        mul_le_mul_of_nonneg_left hp (sq_nonneg _)
      _ = (2 * t * r) * ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 * _) := by ring
      _ ≤ (2 * t * r) * C := mul_le_mul_of_nonneg_left hk' (by positivity)
  obtain ⟨hs, hv⟩ := nonzero_lattice_envelope_sum t ((2 * t * r) * C) ht (by positivity)
    _ (fun h => dualMiddleAt_nonneg W S T rows left right (a h.val) (b h.val) M F h.val) hpoint
  refine ⟨hs, (mul_le_mul_iff_right₀ ht).mp ?_⟩
  calc
    _ ≤ nonzeroLatticeEnvelopeConstant * ((2 * t * r) * C) := hv
    _ = _ := by dsimp only [C, r]; ring

end

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem divisorExponentConstant_pos {α : ℝ} (h : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    0 < divisorExponentConstant h deltaLoss hδ := (h.divisor_pair deltaLoss hδ).choose_spec.1

theorem divisor_cost_with_constant {α : ℝ} (h : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    {n p : Type*} [Fintype n] [Fintype p]
    (ε : ℝ) (hε : 0 < ε) (B N D₁ D₂ : ℝ)
    (hB : 1 ≤ B) (hN : 1 ≤ N) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂)
    (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N) (a : n → ℂ) (b : p → ℂ) :
    Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) ≤
      divisorEnergyFactor ε hε N a b *
        (divisorExponentConstant h deltaLoss hδ * (B * N) ^ deltaLoss * (N + B ^ α * (D₁ * D₂))) := by
  rw [divisorBlockCost_sqrt ε hε D₁ D₂ B N (by linarith) (by linarith) a b]
  exact mul_le_mul_of_nonneg_left
    ((h.divisor_pair deltaLoss hδ).choose_spec.2 B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N)
    (divisorEnergyFactor_nonneg ε hε N a b)

theorem sqrt_div_mul_rpow (M B α : ℝ) (hM : 0 ≤ M) (hB : 0 < B) :
    Real.sqrt (M / B) * B ^ α = Real.sqrt M * B ^ (α - 1 / 2) := by
  rw [Real.rpow_sub hB, ← Real.sqrt_eq_rpow, Real.sqrt_div hM]
  ring

theorem dual_middle_scale_shape (M F B N D T α : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 < B) (hN : 0 < N)
    (hD : D ≤ T * (N * Real.sqrt (F / (M * B)))) :
    (M / (F * N)) * (N + B ^ α * D) ≤
      M / F + T * Real.sqrt (M / F) * B ^ (α - 1 / 2) := by
  have hratio : 0 ≤ M / (F * N) := by positivity
  calc
    _ ≤ (M / (F * N)) * (N + B ^ α * (T * (N * Real.sqrt (F / (M * B))))) := by gcongr
    _ = M / F + T * (Real.sqrt ((M / F) / B) * B ^ α) := by
      rw [dual_middle_scale_identity M F B N hM hF hB hN]
      field_simp

    _ = _ := by rw [sqrt_div_mul_rpow (M / F) B α (by positivity) hB]; ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
variable {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
  (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M U : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
  (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
  (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
  (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)

include hD₁ hD₂ hB hN hD₁N hD₂N hM hS hT hr hl hri hrows ha hb

theorem HasSieveExponent.dual_middle_block
    (W : 𝓢(ℝ, ℂ)) (F : ℝ) (hF : 0 < F)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hcut : D₁ * D₂ ≤ U * (N * Real.sqrt (F / (M * B)))) :
    (∑' h : {h : O // h ≠ 0},
      dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val) ≤
      (2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
          (M / F + U * Real.sqrt (M / F) * B ^ (α - 1 / 2)) := by
  have hc := divisor_cost_with_constant hexp deltaLoss hδ ε hε B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N a₀ b₀
  have hs := (actual_dual_middle_all_frequencies ε hε S T D₁ D₂ B N M F hD₁ hD₂ hB hN hM hF hS hT
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W hleft hright).2
  have hk : 0 ≤ 2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W :=
    mul_nonneg (mul_nonneg (by norm_num) nonzeroLatticeEnvelopeConstant_nonneg) (dualMiddleDecayConstant_nonneg W)
  have hf := divisorEnergyFactor_nonneg ε hε N a₀ b₀
  have hconst := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  calc
    _ ≤ ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) * (M / (F * N))) *
        (divisorEnergyFactor ε hε N a₀ b₀ *
          (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss * (N + B ^ α * (D₁ * D₂)))) :=
      hs.trans (mul_le_mul_of_nonneg_left hc (by positivity))
    _ = ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss)) *
          ((M / (F * N)) * (N + B ^ α * (D₁ * D₂))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (dual_middle_scale_shape M F B N (D₁ * D₂) U α hM hF (by linarith) (by linarith) hcut) (by positivity)

end CanonicalQuadraticSieve

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.SupportNorms
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem sqrt_scale_shell_upper (M B b : ℝ) (hM : 0 < M) (hB : 0 < B)
    (hb : B / 2 ≤ b) : Real.sqrt (M / b) ≤ 2 * Real.sqrt (M / B) := by
  simpa only [one_mul, div_one] using principal_middle_prefactor_bound
    M B b 1 1 1 1 hM hB hb (by norm_num) le_rfl (by norm_num) le_rfl

theorem original_middle_rectangle_upper (M B b D₁ D₂ d e U : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : B / 2 ≤ b) (hU : 0 ≤ U)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hd : D₁ ≤ d) (he : D₂ ≤ e)
    (hcut : d * e ≤ U * Real.sqrt (M / b)) :
    D₁ * D₂ ≤ (2 * U) * Real.sqrt (M / B) := by
  calc
    _ ≤ d * e := mul_le_mul hd he hD₂ (hD₁.trans hd)
    _ ≤ U * Real.sqrt (M / b) := hcut
    _ ≤ U * (2 * Real.sqrt (M / B)) :=
      mul_le_mul_of_nonneg_left (sqrt_scale_shell_upper M B b hM hB hb) hU
    _ = _ := by ring

theorem dual_middle_rectangle_upper (M F B b N D₁ D₂ d e U : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 < B) (hb : B / 2 ≤ b) (hN : 0 ≤ N) (hU : 0 ≤ U)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hd : D₁ ≤ d) (he : D₂ ≤ e)
    (hcut : d * e ≤ U * (N * Real.sqrt (F / (M * b)))) :
    D₁ * D₂ ≤ (2 * U) * (N * Real.sqrt (F / (M * B))) := by
  have harg (z : ℝ) : F / (M * z) = (F / M) / z := by ring
  simp only [harg] at hcut ⊢
  have hh := original_middle_rectangle_upper (F / M) B b D₁ D₂ d e (U * N)
    (div_pos hF hM) hB hb (mul_nonneg hU hN) hD₁ hD₂ hd he
    (by simpa only [mul_assoc] using hcut)
  simpa only [mul_assoc] using hh

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleWindowAt_bounds (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) :
    0 ≤ dualMiddleWindowAt W S T rows left right a b M F P h ∧
    dualMiddleWindowAt W S T rows left right a b M F P h ≤
      dualMiddleAt W S T rows left right a b M F h := by
  classical
  constructor
  · unfold dualMiddleWindowAt
    positivity
  · unfold dualMiddleWindowAt dualMiddleAt
    gcongr with D _ E _ i _
    split_ifs <;> first | exact le_rfl | positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleWindowAt_eq_zero (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O)
    (hP : ∀ (D : S) (E : T) i, ¬ P (D.val * E.val) i) :
    dualMiddleWindowAt W S T rows left right a b M F P h = 0 := by
  classical
  simp only [dualMiddleWindowAt, hP, ite_false, Finset.sum_const_zero]

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.MiddleWindows
namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

section

open scoped BigOperators Classical SchwartzMap

section
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
variable {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
  (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M U : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
  (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
  (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
  (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)

include hD₁ hD₂ hB hN hD₁N hD₂N hM hS hT hr hl hri hrows ha hb

theorem HasSieveExponent.dual_middle_window
    (hU : 0 ≤ U) (W : 𝓢(ℝ, ℂ)) (F : ℝ) (hF : 0 < F) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ (D : S) (E : T) i, P (D.val * E.val) i →
      (Ideal.absNorm (D.val * E.val) : ℝ) ≤ U *
        (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) ≤
      (2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
          (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2)) := by
  have hs0 := (actual_dual_middle_all_frequencies ε hε S T D₁ D₂ B N M F hD₁ hD₂ hB hN hM hF hS hT
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W hleft hright).1
  have hbounds (h : {h : O // h ≠ 0}) :=
    dualMiddleWindowAt_bounds W S T rows left right (a h.val) (b h.val) M F P h.val
  have hs := Summable.of_nonneg_of_le (fun h => (hbounds h).1) (fun h => (hbounds h).2) hs0
  refine ⟨hs, ?_⟩
  by_cases hcut : D₁ * D₂ ≤ (2 * U) * (N * Real.sqrt (F / (M * B)))
  · exact (hs.tsum_le_tsum (fun h => (hbounds h).2) hs0).trans
      (hexp.dual_middle_block deltaLoss hδ ε hε S T D₁ D₂ B N M (2 * U)
        hD₁ hD₂ hB hN hD₁N hD₂N hM hS hT rows left right hr hl hri hrows a₀ b₀ a b ha hb W F hF hleft hright hcut)
  · have hp (D : S) (E : T) (i : m) : ¬ P (D.val * E.val) i := by
      intro hh
      apply hcut
      apply dual_middle_rectangle_upper M F B (Ideal.absNorm (rows i)) N D₁ D₂
        (Ideal.absNorm D.val) (Ideal.absNorm E.val) U hM hF (by linarith) (hrows i).2.1 (by linarith) hU
        (by linarith) (by linarith) (hS D.val D.property).1 (hT E.val E.property).1
      simpa only [map_mul, Nat.cast_mul] using hP D E i hh
    have hz : (fun h : {h : O // h ≠ 0} =>
        dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) = fun _ => 0 :=
      funext (fun h => dualMiddleWindowAt_eq_zero W S T rows left right (a h.val) (b h.val) M F P h.val hp)
    rw [hz, tsum_zero]
    have h1 := nonzeroLatticeEnvelopeConstant_nonneg
    have h2 := dualMiddleDecayConstant_nonneg W
    have h3 := divisorEnergyFactor_nonneg ε hε N a₀ b₀
    have h4 := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity

end

section
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FourierBridge

theorem large_principal_scale_shape (X N Q D V : ℝ) (hD : 0 < D)
    (hcut : X * N ≤ V * D) :
    (X / D) * (N + Q * D) ≤ V + X * Q := by
  have hh : X * N / D ≤ V := (div_le_iff₀ hD).mpr hcut
  calc
    _ = X * N / D + X * Q := by field_simp
    _ ≤ _ := add_le_add hh le_rfl

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

variable (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
  (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
  (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
  (a : n → ℂ) (b : p → ℂ)

include hD₁ hD₂ hB hN hM hS hT hr hl hri hrows hleft hright

theorem principalCorrectionAt_bound :
    principalCorrectionAt S T rows left right a b M ≤
      (2 * Real.sqrt (M / B) / (D₁ * D₂)) *
        Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) := by
  have hh := canonical_original_divisor_block_phase_bound ε hε S T D₁ D₂ B N hD₁ hD₂ hN hS hT
    rows left right hr hl hri (fun i => ⟨(hrows i).1, (hrows i).2.2⟩) hleft hright a b
    (fun _ => 0) (fun _ => 0) 0
  simp only [zero_add, logPhase_zero, mul_one] at hh
  have heq : (∑ D : S, ∑ E : T, ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k‖) =
      ∑ D ∈ S, ∑ E ∈ T, ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k‖ := by
    rw [Finset.sum_coe_sort S (fun D => ∑ E : T, ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a b D E.val i j k‖)]
    apply Finset.sum_congr rfl
    intro D hD
    exact Finset.sum_coe_sort T (fun E => ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k‖)
  have hp := principal_middle_prefactor_sum S T rows
    (fun D E i => ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k‖)
    (fun _ _ _ => norm_nonneg _) M B D₁ D₂ hM (by linarith) (by linarith) (by linarith)
    (fun i => (hrows i).2.1) (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)
  change principalCorrectionAt S T rows left right a b M ≤ _ at hp
  rw [heq] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left hh (by positivity))

theorem HasSieveExponent.large_principal_correction {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N) (V : ℝ)
    (hcut : Real.sqrt (M / B) * N ≤ V * (D₁ * D₂)) :
    principalCorrectionAt S T rows left right a b M ≤
      2 * divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
        (V + Real.sqrt M * B ^ (α - 1 / 2)) := by
  have hb := principalCorrectionAt_bound ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT
    rows left right hr hl hri hrows hleft hright a b
  have hc := divisor_cost_with_constant hexp deltaLoss hδ ε hε B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N a b
  have hf := divisorEnergyFactor_nonneg ε hε N a b
  have hconst := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  calc
    _ ≤ (2 * Real.sqrt (M / B) / (D₁ * D₂)) *
        (divisorEnergyFactor ε hε N a b *
          (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss * (N + B ^ α * (D₁ * D₂)))) :=
      hb.trans (mul_le_mul_of_nonneg_left hc (by positivity))
    _ = (2 * divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss)) *
        ((Real.sqrt (M / B) / (D₁ * D₂)) * (N + B ^ α * (D₁ * D₂))) := by ring
    _ ≤ (2 * divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss)) *
        (V + Real.sqrt (M / B) * B ^ α) := mul_le_mul_of_nonneg_left
      (large_principal_scale_shape _ _ _ _ _ (by positivity) hcut) (by positivity)
    _ = _ := by rw [sqrt_div_mul_rpow M B α hM.le (by linarith)]

end

section
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem sum_two_subtype_pools {A : Type*} [AddCommMonoid A]
    (S T : Finset (Ideal O)) (f : Ideal O → Ideal O → A) :
    (∑ D : S, ∑ E : T, f D.val E.val) = ∑ D ∈ S, ∑ E ∈ T, f D E := by
  rw [Finset.sum_coe_sort S (fun D => ∑ E : T, f D E.val)]
  apply Finset.sum_congr rfl
  intro D hD
  exact Finset.sum_coe_sort T (f D)

end

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleWindowAt_eq_finset (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) :
    dualMiddleWindowAt W S T rows left right a b M F P h =
      ∑ D ∈ S, ∑ E ∈ T, ∑ i, if P (D * E) i then
        (Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) /
          ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ))) *
        ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * paperRadialFourier W
          (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) / (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
            ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ)))‖ else 0 := by
  classical
  unfold dualMiddleWindowAt
  exact sum_two_subtype_pools (A := ℝ) S T (fun D E => ∑ i, if P (D * E) i then
    (Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * paperRadialFourier W
      (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) / (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
        ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ)))‖ else 0)

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleWindowAt_dyadic (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O)) (N : ℝ)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) :
    dualMiddleWindowAt W S T rows left right a b M F P h =
      ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1),
        dualMiddleWindowAt W (divisorDyadicBin S N j) (divisorDyadicBin T N k)
          rows left right a b M F P h := by
  classical
  simp_rw [dualMiddleWindowAt_eq_finset]
  exact sum_divisorDyadicRectangles (A := ℝ) S T N _

theorem HasSieveExponent.dual_middle_pool {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (S T : Finset (Ideal O)) (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N)
    (hT : ∀ E ∈ T, 1 ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ N)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ (D : S) (E : T) i, P (D.val * E.val) i →
      (Ideal.absNorm (D.val * E.val) : ℝ) ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2))) := by
  classical
  let V := (2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2))
  have hV : 0 ≤ V := by
    have h1 := nonzeroLatticeEnvelopeConstant_nonneg
    have h2 := dualMiddleDecayConstant_nonneg W
    have h3 := divisorEnergyFactor_nonneg ε hε N a₀ b₀
    have h4 := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    dsimp only [V]
    positivity
  let f := fun (j k : Fin (columnDyadicLength N + 1)) (h : {h : O // h ≠ 0}) =>
    dualMiddleWindowAt W (divisorDyadicBin S N j) (divisorDyadicBin T N k)
      rows left right (a h.val) (b h.val) M F P h.val
  have hf (j k : Fin (columnDyadicLength N + 1)) : Summable (f j k) ∧ (∑' h, f j k h) ≤ V := by
    by_cases hSj : (divisorDyadicBin S N j).Nonempty
    · by_cases hTk : (divisorDyadicBin T N k).Nonempty
      · exact hexp.dual_middle_window deltaLoss hδ ε hε (divisorDyadicBin S N j) (divisorDyadicBin T N k)
          (divisorDyadicScale j.val) (divisorDyadicScale k.val) B N M U
          (divisorDyadicScale_ge_one _) (divisorDyadicScale_ge_one _) hB hN
          (divisorDyadicBin_scale_le S N hS j hSj) (divisorDyadicBin_scale_le T N hT k hTk)
          hM (divisorDyadicBin_bounds S N hS j) (divisorDyadicBin_bounds T N hT k)
          rows left right hr hl hri hrows a₀ b₀ a b ha hb hU W F hF P hleft hright
          (fun D E i hp => hP
            ⟨D.val, (Finset.mem_filter.mp D.property).1⟩
            ⟨E.val, (Finset.mem_filter.mp E.property).1⟩ i hp)
      · have hz := Finset.not_nonempty_iff_eq_empty.mp hTk
        have he : f j k = fun _ => 0 := by
          funext h
          apply dualMiddleWindowAt_eq_zero
          intro D E i hp
          have hh := E.property
          simp only [hz, Finset.notMem_empty] at hh
        rw [he]
        simpa only [tsum_zero] using And.intro (summable_zero : Summable (fun _ : {h : O // h ≠ 0} => (0 : ℝ))) hV
    · have hz := Finset.not_nonempty_iff_eq_empty.mp hSj
      have he : f j k = fun _ => 0 := by
        funext h
        apply dualMiddleWindowAt_eq_zero
        intro D E i hp
        have hh := D.property
        simp only [hz, Finset.notMem_empty] at hh
      rw [he]
      simpa only [tsum_zero] using And.intro (summable_zero : Summable (fun _ : {h : O // h ≠ 0} => (0 : ℝ))) hV
  have he : (fun h : {h : O // h ≠ 0} =>
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) =
      fun h => ∑ j, ∑ k, f j k h := by
    funext h
    exact dualMiddleWindowAt_dyadic W S T N rows left right (a h.val) (b h.val) M F P h.val
  rw [he]
  refine ⟨summable_sum (fun j _ => summable_sum (fun k _ => (hf j k).1)), ?_⟩
  rw [Summable.tsum_finsetSum (fun j _ => summable_sum (fun k _ => (hf j k).1))]
  calc
    _ = ∑ j, ∑ k, ∑' h, f j k h := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Summable.tsum_finsetSum (fun k _ => (hf j k).1)
    _ ≤ ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1), V :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => (hf j k).2))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, V, pow_two]; ring

end

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.GreenIntegrals
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem norm_double_sum_real_factor_fun {n p : Type*} [Fintype n] [Fintype p]
    (u z : n → p → ℂ) (c : ℝ) (hc : 0 ≤ c) :
    ‖∑ j, ∑ k, u j k * ((c : ℂ) * z j k)‖ = c * ‖∑ j, ∑ k, u j k * z j k‖ := by
  have he : (∑ j, ∑ k, u j k * ((c : ℂ) * z j k)) =
      (c : ℂ) * ∑ j, ∑ k, u j k * z j k := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualProductDivisorMiddleAt_nonneg (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) :
    0 ≤ dualProductDivisorMiddleAt W K rows left right a b M F P h := by
  classical
  unfold dualProductDivisorMiddleAt
  positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualProductDivisorMiddleAt_le_window
    (W : 𝓢(ℝ, ℂ)) (K S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T) :
    dualProductDivisorMiddleAt W K rows left right a b M F P h ≤
      dualMiddleWindowAt W S T rows left right a b M F (fun d i => d ∈ K ∧ P d i) h := by
  classical
  have hp (i : m) := originalColumnSum_divisor_rectangles K S T rows left right a b i
    hleft hright hS hT P (fun d i j k => dualPrincipalKernel W rows left right M F h d i j k)
  apply (Finset.sum_le_sum (fun i _ => hp i)).trans_eq
  rw [dualMiddleWindowAt_eq_finset]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E hE
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hd : D * E ∈ K
  · by_cases hpi : P (D * E) i
    · simp only [hd, hpi, and_self, ite_true]
      unfold dualPrincipalKernel
      simp only [map_mul, Nat.cast_mul]
      exact norm_double_sum_real_factor_fun _ _ _ (by positivity)
    · simp only [hd, hpi, and_false, ite_false, ite_true]
  · simp only [hd, false_and, ite_false]

theorem HasSieveExponent.dual_product_divisor_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (K : Finset (Ideal O)) (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ d ∈ K, ∀ i, P d i →
      (Ideal.absNorm d : ℝ) ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      dualProductDivisorMiddleAt W K rows left right (a h.val) (b h.val) M F P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      dualProductDivisorMiddleAt W K rows left right (a h.val) (b h.val) M F P h.val) ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2))) := by
  let S := columnDivisorPool left
  let T := columnDivisorPool right
  have hl0 : ∀ j, left j ≠ 0 := fun j => (hleft j).1.1
  have hr0 : ∀ k, right k ≠ 0 := fun k => (hright k).1.1
  have hs := hexp.dual_middle_pool deltaLoss hδ ε hε S T B N M F U hB hN hM hF hU
    (columnDivisorPool_norm_bounds left hl0 N (fun j => (hleft j).2.2))
    (columnDivisorPool_norm_bounds right hr0 N (fun k => (hright k).2.2))
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W (fun d i => d ∈ K ∧ P d i) hleft hright
    (fun D E i hp => hP _ hp.1 i hp.2)
  have hdom (h : {h : O // h ≠ 0}) := dualProductDivisorMiddleAt_le_window W K S T
    rows left right (a h.val) (b h.val) M F P h.val hl0 hr0
    (mem_columnDivisorPool_of_dvd left hl0) (mem_columnDivisorPool_of_dvd right hr0)
  have ht := Summable.of_nonneg_of_le
    (fun h : {h : O // h ≠ 0} => dualProductDivisorMiddleAt_nonneg W K rows left right
      (a h.val) (b h.val) M F P h.val) hdom hs.1
  exact ⟨ht, (ht.tsum_le_tsum hdom hs.1).trans hs.2⟩

end CanonicalQuadraticSieve

open Filter MeasureTheory
open scoped BigOperators Classical Topology

open Filter MeasureTheory
open scoped BigOperators Classical Topology

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.GreenIdentity
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace CanonicalQuadraticSieve

theorem symmetric_truncation_scales (X₀ X T : ℝ) (hX₀ : 0 < X₀)
    (hlo : X₀/2 ≤ X) (hhi : X ≤ 2*X₀) (hT : 4 ≤ T) :
    0 < X ∧ 0 < X₀/T ∧ X₀/T ≤ X ∧ X ≤ T*X₀ ∧ 0 ≤ T^4 := by
  have hT0 : 0 < T := by linarith
  have hX : 0 < X := by linarith
  refine ⟨hX,div_pos hX₀ hT0,?_,?_,by positivity⟩
  · apply (div_le_iff₀ hT0).mpr
    nlinarith
  · nlinarith

theorem symmetric_truncation_scalar_bound (m : ℕ) (X₀ X T : ℝ) (hX₀ : 0 < X₀)
    (hlo : X₀/2 ≤ X) (hhi : X ≤ 2*X₀) (hT : 4 ≤ T) :
    ((X₀/T)/X)^(m+3) + 1/(1+(T*X₀)/X)^(m+3) +
      (X/(X₀/T))/((min 1 (X/(T*X₀)))^2*(1+X*T^4/(T*X₀))^(m+3)) ≤
      (2 : ℝ)^(m+10)/T^m := by
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hX : 0 < X := by linarith
  have hY : 0 < X₀/T := div_pos hX₀ hT0
  have hratio : (X₀/T)/X ≤ 2/T := by
    apply (div_le_iff₀ hX).mpr
    calc
      X₀/T ≤ (2*X)/T := div_le_div_of_nonneg_right (by linarith) hT0.le
      _ = (2/T)*X := by ring
  have hinv : 1/(1+(T*X₀)/X) ≤ 2/T := by
    have hz : T/2 ≤ (T*X₀)/X := (le_div_iff₀ hX).mpr (by nlinarith)
    calc
      _ ≤ 1/(T/2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      _ = 2/T := by field_simp
  have hpow : (2/T)^(m+3) ≤ (2 : ℝ)^(m+3)/T^m := by
    rw [div_pow]
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hT0 m)
      (pow_le_pow_right₀ hT1 (by omega : m ≤ m+3))
  have h₁ : ((X₀/T)/X)^(m+3) ≤ (2 : ℝ)^(m+3)/T^m :=
    (pow_le_pow_left₀ (by positivity) hratio _).trans hpow
  have h₂ : 1/(1+(T*X₀)/X)^(m+3) ≤ (2 : ℝ)^(m+3)/T^m := by
    simpa only [div_pow,one_pow] using (pow_le_pow_left₀ (by positivity) hinv (m+3)).trans hpow
  have hnum : X/(X₀/T) ≤ 2*T := by
    apply (div_le_iff₀ hY).mpr
    have he : 2*T*(X₀/T) = 2*X₀ := by field_simp
    rw [he]
    exact hhi
  have hmin : 1/(2*T) ≤ min 1 (X/(T*X₀)) := by
    apply le_min
    · apply (div_le_iff₀ (by positivity : 0 < 2*T)).mpr
      linarith
    · apply (le_div_iff₀ (mul_pos hT0 hX₀)).mpr
      have he : 1/(2*T)*(T*X₀)=X₀/2 := by field_simp
      rwa [he]
  have hfreq : T ≤ 1+X*T^4/(T*X₀) := by
    have ht2 : 2 ≤ T^2 := by nlinarith
    have ht4 : 2*T^2 ≤ T^4 := by nlinarith [sq_nonneg (T^2-2)]
    have hprod : T*(T*X₀) ≤ X*T^4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sq_nonneg (T^2))]
    have hh := (le_div_iff₀ (mul_pos hT0 hX₀)).mpr hprod
    linarith
  have hden : (1/(2*T))^2*T^(m+3) ≤
      (min 1 (X/(T*X₀)))^2*(1+X*T^4/(T*X₀))^(m+3) := by
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) hmin 2)
      (pow_le_pow_left₀ hT0.le hfreq (m+3)) (by positivity) (by positivity)
  have h₃ : (X/(X₀/T))/((min 1 (X/(T*X₀)))^2*(1+X*T^4/(T*X₀))^(m+3)) ≤ 8/T^m := by
    calc
      _ ≤ (2*T)/((1/(2*T))^2*T^(m+3)) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = _ := by rw [pow_add]; field_simp; ring
  have hc : 2*(2 : ℝ)^(m+3)+8 ≤ (2 : ℝ)^(m+10) := by
    have hm : 1 ≤ (2 : ℝ)^m := one_le_pow₀ (by norm_num)
    rw [pow_add,pow_add]
    norm_num
    nlinarith
  calc
    _ ≤ (2 : ℝ)^(m+3)/T^m + (2 : ℝ)^(m+3)/T^m + 8/T^m := add_le_add (add_le_add h₁ h₂) h₃
    _ = (2*(2 : ℝ)^(m+3)+8)/T^m := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hc (by positivity)

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.CuspIntegration
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem sum_subtype_powerset_products (S : Finset (Ideal O)) (f : Ideal O → ℂ) :
    (∑ E ∈ (Finset.univ : Finset S).powerset, f (∏ P ∈ E, P.val)) =
      ∑ E ∈ S.powerset, f (∏ P ∈ E, P) := by
  classical
  have hS : (Finset.univ : Finset S).image Subtype.val = S := by
    ext P
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists, exists_prop,
      exists_eq_right]
  conv_rhs => rw [← hS, Finset.powerset_image]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro E hE
    congr 1
    rw [Finset.prod_image]
    exact fun _ _ _ _ h => Subtype.val_injective h
  · exact fun _ _ _ _ h => Finset.image_injective Subtype.val_injective h

theorem primePool_singleton_eq_primeSupport (G : Ideal O) :
    primePool {G} = primeSupport G := by
  simp [primePool, primeSupport]

theorem primePool_subset_sum_eq_divisors (G : Ideal O) (hG : Squarefree G) (f : Ideal O → ℂ) :
    (∑ E ∈ (Finset.univ : Finset (primePool {G})).powerset,
      f (∏ P ∈ E, P.val)) = ∑ d ∈ idealDivisors G, f d := by
  rw [sum_subtype_powerset_products, primePool_singleton_eq_primeSupport]
  exact (squarefree_divisor_sum_eq_support G hG f).symm

theorem middleTruncation_eq_ideal_divisors (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) :
    middleTruncation (fun P : primePool {G} => P.val) Finset.univ W X Y Z lengthScale =
      (X : ℂ) * ∑ d ∈ idealDivisors G,
        if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
          (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) *
            ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊,
              paperRadialFourier W ((X / (Ideal.absNorm d : ℝ)) * ‖eisEmbedding h‖ ^ 2)
        else 0 := by
  classical
  let f : Ideal O → ℂ := fun d =>
    if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
      (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) *
        ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊,
          paperRadialFourier W ((X / (Ideal.absNorm d : ℝ)) * ‖eisEmbedding h‖ ^ 2)
    else 0
  change middleTruncation _ _ W X Y Z lengthScale = (X : ℂ) * ∑ d ∈ idealDivisors G, f d
  rw [← primePool_subset_sum_eq_divisors G hG f]
  unfold middleTruncation middleDivisors smallDivisors
  simp only [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only [f, subsetNorm, subsetMobius]
  push_cast
  by_cases hY : Y < (Ideal.absNorm (∏ P ∈ E, P.val) : ℝ) <;>
    by_cases hZ : (Ideal.absNorm (∏ P ∈ E, P.val) : ℝ) ≤ Z <;> simp only [hY, hZ, and_self,
      false_and, and_false, ite_true, ite_false]

theorem middleTruncation_eq_ideal_frequencies (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) :
    middleTruncation (fun P : primePool {G} => P.val) Finset.univ W X Y Z lengthScale =
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, ∑ d ∈ idealDivisors G,
        if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
          (UniqueFactorizationMonoid.moebius d : ℂ) *
            (((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
              paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ)))
        else 0 := by
  classical
  rw [middleTruncation_eq_ideal_divisors G hG, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hc : Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z
  · simp only [hc, and_self, ite_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    have harg : (X / (Ideal.absNorm d : ℝ)) * ‖eisEmbedding h‖ ^ 2 =
        X * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ) := by ring
    rw [harg]
    push_cast
    ring
  · simp only [hc, ite_false, mul_zero, Finset.sum_const_zero]

theorem principalTruncation_eq_ideal_divisors (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (X Z : ℝ) :
    principalTruncation (fun P : primePool {G} => P.val) Finset.univ W X Z =
      (X : ℂ) * paperRadialFourier W 0 *
        (∏ P : primePool {G}, (1 - (1 : ℂ) / Ideal.absNorm P.val)) -
      (X : ℂ) * paperRadialFourier W 0 *
        (∑ d ∈ idealDivisors G, if Z < (Ideal.absNorm d : ℝ) then
          (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) else 0) -
      W 0 * (∑ d ∈ idealDivisors G, if (Ideal.absNorm d : ℝ) ≤ Z then
        (UniqueFactorizationMonoid.moebius d : ℂ) else 0) := by
  classical
  rw [← primePool_subset_sum_eq_divisors G hG
    (fun d => if Z < (Ideal.absNorm d : ℝ) then
      (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) else 0),
    ← primePool_subset_sum_eq_divisors G hG
    (fun d => if (Ideal.absNorm d : ℝ) ≤ Z then (UniqueFactorizationMonoid.moebius d : ℂ) else 0)]
  unfold principalTruncation largeDivisors smallDivisors
  simp only [Finset.sum_filter, subsetNorm, subsetMobius, Complex.ofReal_natCast]

end

open ActualEisensteinCubic

theorem finite_middle_triangle
    {m n p H D : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype H] [Fintype D]
    (muCoefficient : D → ℂ) (hμ : ∀ d, ‖muCoefficient d‖ ≤ 1) (A : m → n → p → H → D → ℂ) :
    ‖∑ i, ∑ j, ∑ k, ∑ h, ∑ d, muCoefficient d * A i j k h d‖ ≤
      ∑ h, ∑ i, ∑ d, ‖∑ j, ∑ k, A i j k h d‖ := by
  classical
  have he : (∑ i, ∑ j, ∑ k, ∑ h, ∑ d, muCoefficient d * A i j k h d) =
      ∑ h, ∑ i, ∑ d, muCoefficient d * (∑ j, ∑ k, A i j k h d) := by
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset p)) (t := (Finset.univ : Finset H)),
      Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset H)),
      Finset.sum_comm (s := (Finset.univ : Finset m)) (t := (Finset.univ : Finset H)),
      Finset.sum_comm (s := (Finset.univ : Finset p)) (t := (Finset.univ : Finset D)),
      Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset D))]
    simp only [Finset.mul_sum]
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro h hh
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hμ d)

theorem finite_nonzero_frequency_sum_le (H : Finset O) (hH : ∀ h ∈ H, h ≠ 0)
    (f : O → ℝ) (hf : ∀ h, 0 ≤ f h)
    (hs : Summable (fun h : {h : O // h ≠ 0} => f h.val)) :
    (∑ h ∈ H, f h) ≤ ∑' h : {h : O // h ≠ 0}, f h.val := by
  classical
  let e : H → {h : O // h ≠ 0} := fun h => ⟨h.val, hH h.val h.property⟩
  have he : Function.Injective e := by
    intro h k hh
    apply Subtype.ext
    exact congrArg (fun x : {h : O // h ≠ 0} => x.val) hh
  have hsH : Summable (fun h : H => f h.val) :=
    summable_of_hasFiniteSupport (Set.toFinite _)
  have hb := hsH.tsum_le_tsum_of_inj e he (fun h _ => hf h.val) (fun _ => le_rfl) hs
  rw [tsum_fintype, Finset.sum_coe_sort H f] at hb
  exact hb

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem sum_two_finite_subtypes {α β A : Type*} [AddCommMonoid A]
    (S : Finset α) (T : Finset β) (f : α → β → A) :
    (∑ a : S, ∑ b : T, f a.val b.val) = ∑ a ∈ S, ∑ b ∈ T, f a b := by
  rw [Finset.sum_coe_sort S (fun a => ∑ b : T, f a b.val)]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_coe_sort T (f a))

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.DualMiddleExpansion
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem scaled_middleTruncation_eq_ideal_frequencies (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (c X Y Z lengthScale : ℝ) :
    (c : ℂ) * middleTruncation (fun P : primePool {G} => P.val) Finset.univ W X Y Z lengthScale =
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, ∑ d ∈ idealDivisors G,
        if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
          (UniqueFactorizationMonoid.moebius d : ℂ) *
            ((((c * X) / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
              paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ)))
        else 0 := by
  classical
  rw [middleTruncation_eq_ideal_frequencies G hG]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hp : Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z
  · simp only [hp, and_self, ite_true]
    push_cast
    ring
  · simp only [hp, ite_false, mul_zero]

theorem dual_normalized_middle_expansion (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (M F b i j Y Z lengthScale : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hb : 0 < b) (hi : 0 < i) (hj : 0 < j) :
    ((M / (Real.sqrt (i * j) * F) : ℝ) : ℂ) *
      middleTruncation (fun P : primePool {G} => P.val) Finset.univ W
        (Real.sqrt (F * i * j / (M * b))) Y Z lengthScale =
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, ∑ d ∈ idealDivisors G,
        if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
          (UniqueFactorizationMonoid.moebius d : ℂ) *
            (((Real.sqrt ((M / F) / b) / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
              paperRadialFourier W
                (Real.sqrt (F * i * j / (M * b)) * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ)))
        else 0 := by
  rw [scaled_middleTruncation_eq_ideal_frequencies G hG,
    dual_principal_prefactor_identity M F b i j hM hF hb hi hj]

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dual_truncated_pair_expansion
    (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hrows : ∀ i, Admissible (rows i))
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hK : ∀ j k d, d ∣ left j * right k → d ∈ K) (i : m) (j : n) (k : p) :
    originalTerm rows left right a b 1 1 i j k *
      (((M / (Real.sqrt ((Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ)) * F) : ℝ) : ℂ) *
        middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
          (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
            (M * (Ideal.absNorm (rows i) : ℝ)))) (Y i) (Z i) lengthScale) =
      ∑ h : rowNormDisk ⌊lengthScale⌋₊, ∑ d : K, (UniqueFactorizationMonoid.moebius d.val : ℂ) *
        (if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
          if d.val ∣ left j * right k then
            originalTerm rows left right a b 1 1 i j k *
              dualPrincipalKernel W rows left right M F h.val d.val i j k
          else 0 else 0) := by
  classical
  rw [sum_two_finite_subtypes (rowNormDisk ⌊lengthScale⌋₊) K (fun h d =>
    (UniqueFactorizationMonoid.moebius d : ℂ) *
      (if Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i then
        if d ∣ left j * right k then
          originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h d i j k
        else 0 else 0))]
  by_cases hc : IsCoprime (left j) (right k)
  · have hsq : Squarefree (left j * right k) :=
      squarefree_mul_iff.mpr ⟨hc.isRelPrime, (hleft j).2.1, (hright k).2.1⟩
    have hpos (I : Ideal O) (hI : Admissible I) : 0 < (Ideal.absNorm I : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h => hI.1 (Ideal.absNorm_eq_zero_iff.mp h))
    rw [dual_normalized_middle_expansion _ hsq _ _ _ _ _ _ _ _ _ hM hF
      (hpos _ (hrows i)) (hpos _ (hleft j)) (hpos _ (hright k)), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    rw [← divisorPool_filter K (left j * right k) hsq.ne_zero (hK j k), Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdv : d ∣ left j * right k
    · by_cases hp : Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i
      · simp only [hdv, hp, and_self, ite_true, dualPrincipalKernel]
        ring
      · simp only [hdv, hp, ite_true, ite_false, mul_zero]
    · simp only [hdv, ite_false, ite_self, mul_zero]
  · have hz : originalTerm rows left right a b 1 1 i j k = 0 := by simp only [originalTerm, hc, ite_false]
    simp only [hz, zero_mul, ite_self, mul_zero, Finset.sum_const_zero]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualTruncatedMiddle_le_product_divisors
    (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hrows : ∀ i, Admissible (rows i))
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hK : ∀ j k d, d ∣ left j * right k → d ∈ K) :
    ‖dualTruncatedMiddle W rows left right a b M F Y Z lengthScale‖ ≤
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, dualProductDivisorMiddleAt W K rows left right a b M F
        (fun d i => Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i) h := by
  classical
  let A : m → n → p → rowNormDisk ⌊lengthScale⌋₊ → K → ℂ := fun i j k h d =>
    if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
      if d.val ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h.val d.val i j k
      else 0 else 0
  have he : dualTruncatedMiddle W rows left right a b M F Y Z lengthScale =
      ∑ i, ∑ j, ∑ k, ∑ h : rowNormDisk ⌊lengthScale⌋₊, ∑ d : K,
        (UniqueFactorizationMonoid.moebius d.val : ℂ) * A i j k h d := by
    unfold dualTruncatedMiddle
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    exact dual_truncated_pair_expansion W K rows left right a b M F Y Z lengthScale hM hF hrows hleft hright hK i j k
  rw [he]
  apply (finite_middle_triangle (fun d : K => (UniqueFactorizationMonoid.moebius d.val : ℂ))
    (fun d => QuadraticInitialBound.norm_ideal_moebius_le_one d.val) A).trans_eq
  rw [Finset.sum_coe_sort (rowNormDisk ⌊lengthScale⌋₊) (fun h => ∑ i, ∑ d : K,
    ‖∑ j, ∑ k, if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
      if d.val ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h d.val i j k
      else 0 else 0‖)]
  apply Finset.sum_congr rfl
  intro h hh
  unfold dualProductDivisorMiddleAt
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_coe_sort K (fun d =>
    ‖∑ j, ∑ k, if Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i then
      if d ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h d i j k
      else 0 else 0‖)]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hp : Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i <;>
    simp only [hp, and_self, ite_true, ite_false, Finset.sum_const_zero, norm_zero]

theorem HasSieveExponent.dual_truncated_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hZ : ∀ i, Z i ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) :
    ‖dualTruncatedMiddle W rows left right a b M F Y Z lengthScale‖ ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2))) := by
  let pairCols : n × p → Ideal O := fun x => left x.1 * right x.2
  let K := columnDivisorPool pairCols
  have hPair : ∀ x, pairCols x ≠ 0 := fun x => mul_ne_zero (hleft x.1).1.1 (hright x.2).1.1
  have hK (j : n) (k : p) (d : Ideal O) (hd : d ∣ left j * right k) : d ∈ K :=
    mem_columnDivisorPool_of_dvd pairCols hPair (j, k) d hd
  let P : Ideal O → m → Prop := fun d i =>
    Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i
  have hb := hexp.dual_product_divisor_middle deltaLoss hδ ε hε K B N M F U hB hN hM hF hU
    rows left right hr hl hri hrows a b (fun _ => a) (fun _ => b)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) W P hleft hright
    (fun d hd i hp => hp.2.trans (hZ i))
  have hH (h : O) (hh : h ∈ rowNormDisk ⌊lengthScale⌋₊) : h ≠ 0 := by
    intro hz
    have hn := (mem_rowNormDisk.mp hh).1
    simp [hz] at hn
  calc
    _ ≤ ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, dualProductDivisorMiddleAt W K rows left right a b M F P h :=
      dualTruncatedMiddle_le_product_divisors W K rows left right a b M F Y Z lengthScale hM hF (fun i => (hrows i).1)
        (fun j => (hleft j).1) (fun k => (hright k).1) hK
    _ ≤ ∑' h : {h : O // h ≠ 0}, dualProductDivisorMiddleAt W K rows left right a b M F P h.val :=
      finite_nonzero_frequency_sum_le (rowNormDisk ⌊lengthScale⌋₊) hH _
        (fun h => dualProductDivisorMiddleAt_nonneg W K rows left right a b M F P h) hb.1
    _ ≤ _ := hb.2

end CanonicalQuadraticSieve

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SeedDefects
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem sector_bad_good_product (I : Ideal O) (hI : Squarefree I)
    (E : fixedBadPrimes.powerset) (hE : badPrimeSector I = E) :
    sectorBadIdeal E * goodSquarefreePart I = I := by
  have hs : badPrimeSupport I = E.val := congrArg Subtype.val hE
  simpa only [hs, sectorBadIdeal] using squarefree_bad_good_product I hI

theorem sectorBadIdeal_ne_zero_of_row (I : Ideal O) (hI : Squarefree I)
    (E : fixedBadPrimes.powerset) (hE : badPrimeSector I = E) : sectorBadIdeal E ≠ 0 := by
  intro hz
  have hp := sector_bad_good_product I hI E hE
  rw [hz, zero_mul] at hp
  exact hI.ne_zero hp.symm

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem unrestrictedPairTerm_sector (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ)
    (hrows : ∀ i, Squarefree (rows i)) (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) (i : m) (j : n) (k : p) :
    unrestrictedPairTerm rows left right a b i j k =
      originalTerm (fun i => goodSquarefreePart (rows i)) left right
        (fun j => a j * quadraticRow (left j) (idealGenerator (sectorBadIdeal E)))
        (fun k => b k * quadraticRow (right k) (idealGenerator (sectorBadIdeal E))) 1 1 i j k := by
  classical
  by_cases hc : IsCoprime (left j) (right k)
  · simp only [unrestrictedPairTerm, originalTerm, hc, ite_true, one_dvd]
    have hp := unrestrictedPairCharacter_squarefree_bad_split (left j) (right k) (rows i)
      (hleft j) (hright k) (hray j k) (hrows i)
    have hs : badPrimeSupport (rows i) = E.val := congrArg Subtype.val (hE i)
    rw [hp, hs]
    simp only [sectorBadIdeal, unrestrictedPairCharacter, star_mul,
      canonical_quadraticRow_star _ (hleft j)]
    ring
  · simp only [unrestrictedPairTerm, originalTerm, hc, ite_false]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem unrestrictedDualTruncatedMiddle_sector
    (W : 𝓢(ℝ, ℂ)) (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hrows : ∀ i, Squarefree (rows i)) (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E)
    (hQ : sectorBadIdeal E ≠ 0) :
    unrestrictedDualTruncatedMiddle W rows left right a b M F Y Z lengthScale =
      ((1 / (Ideal.absNorm (sectorBadIdeal E) : ℝ) : ℝ) : ℂ) *
        dualTruncatedMiddle W (fun i => goodSquarefreePart (rows i)) left right
          (fun j => a j * quadraticRow (left j) (idealGenerator (sectorBadIdeal E)))
          (fun k => b k * quadraticRow (right k) (idealGenerator (sectorBadIdeal E)))
          (M * (Ideal.absNorm (sectorBadIdeal E) : ℝ)) F Y Z lengthScale := by
  classical
  have hQn : (Ideal.absNorm (sectorBadIdeal E) : ℝ) ≠ 0 := by
    exact_mod_cast (show Ideal.absNorm (sectorBadIdeal E) ≠ 0 from fun h => hQ (Ideal.absNorm_eq_zero_iff.mp h))
  unfold unrestrictedDualTruncatedMiddle dualTruncatedMiddle
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [unrestrictedPairTerm_sector rows left right a b hrows hleft hright hray E hE i j k]
  have hn : (Ideal.absNorm (rows i) : ℝ) =
      (Ideal.absNorm (sectorBadIdeal E) : ℝ) * (Ideal.absNorm (goodSquarefreePart (rows i)) : ℝ) := by
    calc
      (Ideal.absNorm (rows i) : ℝ) =
          (Ideal.absNorm (sectorBadIdeal E * goodSquarefreePart (rows i)) : ℝ) :=
        congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ))
          (sector_bad_good_product (rows i) (hrows i) E (hE i)).symm
      _ = _ := by rw [map_mul, Nat.cast_mul]
  rw [hn]
  have harg : F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
      (M * ((Ideal.absNorm (sectorBadIdeal E) : ℝ) * (Ideal.absNorm (goodSquarefreePart (rows i)) : ℝ))) =
    F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
      ((M * (Ideal.absNorm (sectorBadIdeal E) : ℝ)) * (Ideal.absNorm (goodSquarefreePart (rows i)) : ℝ)) := by ring
  rw [harg]
  have hs : (M / (Real.sqrt ((Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ)) * F) : ℝ) =
      (1 / (Ideal.absNorm (sectorBadIdeal E) : ℝ)) *
        ((M * (Ideal.absNorm (sectorBadIdeal E) : ℝ)) /
          (Real.sqrt ((Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ)) * F)) := by
    field_simp [hQn]
  rw [hs, Complex.ofReal_mul]
  ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss

lemma divisorEnergyFactor_mono_coefficients {n p : Type*} [Fintype n] [Fintype p]
    (ε : ℝ) (hε : 0 < ε) (N : ℝ) (a a' : n → ℂ) (b b' : p → ℂ)
    (ha : ∀ j, ‖a' j‖ ≤ ‖a j‖) (hb : ∀ k, ‖b' k‖ ≤ ‖b k‖) :
    divisorEnergyFactor ε hε N a' b' ≤ divisorEnergyFactor ε hε N a b := by
  have hA : (∑ j, ‖a' j‖ ^ 2) ≤ ∑ j, ‖a j‖ ^ 2 :=
    Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (ha j) _)
  have hB : (∑ k, ‖b' k‖ ^ 2) ≤ ∑ k, ‖b k‖ ^ 2 :=
    Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hb k) _)
  have hs := (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le
  have hd := (DivisorBlockCauchy.divisorConstant_pos ε hε).le
  unfold divisorEnergyFactor
  gcongr

lemma dual_bad_sector_scale (M F B Q U α : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 ≤ B) (hQ : 1 ≤ Q)
    (hU : 0 ≤ U) (hα : 1 / 2 ≤ α) :
    (1 / Q) * (M * Q / F + (2 * U) * Real.sqrt (M * Q / F) * (B / Q) ^ (α - 1 / 2)) ≤
      M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2) := by
  have hQp : 0 < Q := by linarith
  have hpow : (B / Q) ^ (α - 1 / 2) ≤ B ^ (α - 1 / 2) :=
    Real.rpow_le_rpow (by positivity) (div_le_self hB hQ) (by linarith)
  have hsQ : Real.sqrt Q ≤ Q := Real.sqrt_le_self_iff.mpr (Or.inr hQ)
  have hs : (1 / Q) * Real.sqrt (M * Q / F) ≤ Real.sqrt (M / F) := by
    have he : M * Q / F = (M / F) * Q := by ring
    rw [he, Real.sqrt_mul (by positivity)]
    have ht : Real.sqrt Q / Q ≤ 1 := (div_le_one hQp).mpr hsQ
    calc
      _ = Real.sqrt (M / F) * (Real.sqrt Q / Q) := by ring
      _ ≤ Real.sqrt (M / F) * 1 := mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg _)
      _ = _ := mul_one _
  calc
    _ = M / F + (2 * U) * ((1 / Q) * Real.sqrt (M * Q / F)) * (B / Q) ^ (α - 1 / 2) := by
      field_simp

    _ ≤ _ := by gcongr

lemma dualMiddleMajorant_nonneg {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U : ℝ) (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ))
    (hB : 0 ≤ B) (hN : 0 ≤ N) (hM : 0 ≤ M) (hF : 0 ≤ F) (hU : 0 ≤ U) :
    0 ≤ dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W := by
  have hc := nonzeroLatticeEnvelopeConstant_nonneg
  have hW := dualMiddleDecayConstant_nonneg W
  have he := divisorEnergyFactor_nonneg ε hε N a b
  have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  unfold dualMiddleMajorant
  positivity

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem HasSieveExponent.dual_truncated_middle_sector {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1 / 2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Squarefree (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (hZ : ∀ i, Z i ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) :
    ‖unrestrictedDualTruncatedMiddle W rows left right a b M F Y Z lengthScale‖ ≤
      dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W := by
  classical
  cases isEmpty_or_nonempty m with
  | inl hempty =>
    let := hempty
    simp only [unrestrictedDualTruncatedMiddle, Finset.univ_eq_empty, Finset.sum_empty, norm_zero]
    exact dualMiddleMajorant_nonneg hexp deltaLoss hδ ε hε B N M F U a b W (by linarith) (by linarith) hM.le hF.le hU
  | inr hnonempty =>
    let := hnonempty
    let i₀ : m := Classical.choice hnonempty
    let Q : ℝ := Ideal.absNorm (sectorBadIdeal E)
    let good := fun i => goodSquarefreePart (rows i)
    let a' := fun j => a j * quadraticRow (left j) (idealGenerator (sectorBadIdeal E))
    let b' := fun k => b k * quadraticRow (right k) (idealGenerator (sectorBadIdeal E))
    have hQnz := sectorBadIdeal_ne_zero_of_row (rows i₀) (hrows i₀).1 E (hE i₀)
    have hQ : 1 ≤ Q := by
      dsimp only [Q]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun h => hQnz (Ideal.absNorm_eq_zero_iff.mp h)))
    have hQp : 0 < Q := by linarith
    have hn (i : m) : (Ideal.absNorm (rows i) : ℝ) = Q * (Ideal.absNorm (good i) : ℝ) := by
      have hi := congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ))
        (sector_bad_good_product (rows i) (hrows i).1 E (hE i))
      simpa only [map_mul, Nat.cast_mul] using hi.symm
    have hgr : Function.Injective good := by
      intro i k h
      exact hr (goodSquarefreePart_injective_on_sector _ _ (hrows i).1 (hrows k).1
        ((hE i).trans (hE k).symm) h)
    have hg (i : m) : Admissible (good i) ∧ (B / Q) / 2 ≤ (Ideal.absNorm (good i) : ℝ) ∧
        (Ideal.absNorm (good i) : ℝ) ≤ B / Q := by
      refine ⟨goodSquarefreePart_admissible _, ?_, ?_⟩
      · rw [show B / Q / 2 = (B / 2) / Q by ring]
        apply (div_le_iff₀ hQp).2
        have hx := (hrows i).2.1
        rw [hn i] at hx
        nlinarith
      · exact (le_div_iff₀ hQp).2 (by simpa only [mul_comm] using (hn i).symm.trans_le (hrows i).2.2)
    have hBQ : 1 ≤ B / Q := by
      have hh : 1 ≤ (Ideal.absNorm (good i₀) : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun h => (hg i₀).1.1 (Ideal.absNorm_eq_zero_iff.mp h)))
      exact hh.trans (hg i₀).2.2
    have hZa (i : m) : Z i ≤ U * (N * Real.sqrt (F / ((M * Q) * (Ideal.absNorm (good i) : ℝ)))) := by
      simpa only [hn i, mul_assoc] using hZ i
    have hbnd := hexp.dual_truncated_middle deltaLoss hδ ε hε (B / Q) N (M * Q) F U hBQ hN
      (by positivity) hF hU good left right hgr hl hri hg a' b' W Y Z lengthScale hleft hright hZa
    change ‖dualTruncatedMiddle W good left right a' b' (M * Q) F Y Z lengthScale‖ ≤
      dualMiddleMajorant hexp deltaLoss hδ ε hε (B / Q) N (M * Q) F U a' b' W at hbnd
    have htr := unrestrictedDualTruncatedMiddle_sector W rows left right a b M F Y Z lengthScale
      (fun i => (hrows i).1) (fun j => (hleft j).1) (fun k => (hright k).1) hray E hE hQnz
    change unrestrictedDualTruncatedMiddle W rows left right a b M F Y Z lengthScale =
      ((1 / Q : ℝ) : ℂ) * dualTruncatedMiddle W good left right a' b' (M * Q) F Y Z lengthScale at htr
    rw [htr, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / Q)]
    apply (mul_le_mul_of_nonneg_left hbnd (by positivity)).trans
    have hae (j : n) : ‖a' j‖ ≤ ‖a j‖ := by
      dsimp only [a']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)
    have hbe (k : p) : ‖b' k‖ ≤ ‖b k‖ := by
      dsimp only [b']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)
    have he := divisorEnergyFactor_mono_coefficients ε hε N a a' b b' hae hbe
    have hp : ((B / Q) * N) ^ deltaLoss ≤ (B * N) ^ deltaLoss := by
      apply Real.rpow_le_rpow (by positivity) _ hδ.le
      exact mul_le_mul_of_nonneg_right (div_le_self (by linarith) hQ) (by linarith)
    have hs := dual_bad_sector_scale M F B Q U α hM hF (by linarith) hQ hU hα
    have hc := nonzeroLatticeEnvelopeConstant_nonneg
    have hW := dualMiddleDecayConstant_nonneg W
    have hea := divisorEnergyFactor_nonneg ε hε N a' b'
    have heb := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    unfold dualMiddleMajorant
    calc
      _ = ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a' b' * (divisorExponentConstant hexp deltaLoss hδ * ((B / Q) * N) ^ deltaLoss) *
            ((1 / Q) * (M * Q / F + (2 * U) * Real.sqrt (M * Q / F) * (B / Q) ^ (α - 1 / 2)))) := by ring
      _ ≤ _ := by gcongr

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem HasSieveExponent.unrestricted_dual_truncated_middle {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1 / 2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Squarefree (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (hZ : ∀ i, Z i ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) :
    ‖unrestrictedDualTruncatedMiddle W rows left right a b M F Y Z lengthScale‖ ≤
      4 * dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W := by
  classical
  let σ := fun i => badPrimeSector (rows i)
  have hs : unrestrictedDualTruncatedMiddle W rows left right a b M F Y Z lengthScale =
      ∑ E : fixedBadPrimes.powerset,
        unrestrictedDualTruncatedMiddle W (fun i : {i // σ i = E} => rows i.val)
          left right a b M F (fun i => Y i.val) (fun i => Z i.val) lengthScale := by
    unfold unrestrictedDualTruncatedMiddle
    exact (Fintype.sum_fiberwise σ _).symm
  have hb (E : fixedBadPrimes.powerset) :
      ‖unrestrictedDualTruncatedMiddle W (fun i : {i // σ i = E} => rows i.val)
          left right a b M F (fun i => Y i.val) (fun i => Z i.val) lengthScale‖ ≤
        dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W := by
    apply hexp.dual_truncated_middle_sector hα deltaLoss hδ ε hε B N M F U hB hN hM hF hU
      (fun i : {i // σ i = E} => rows i.val) left right
      (fun i k h => Subtype.ext (hr h)) hl hri (fun i => hrows i.val) a b W
      (fun i => Y i.val) (fun i => Z i.val) lengthScale hleft hright hray (fun i => hZ i.val) E
    exact fun i => i.property
  rw [hs]
  calc
    _ ≤ ∑ E : fixedBadPrimes.powerset,
        ‖unrestrictedDualTruncatedMiddle W (fun i : {i // σ i = E} => rows i.val)
          left right a b M F (fun i => Y i.val) (fun i => Z i.val) lengthScale‖ := norm_sum_le _ _
    _ ≤ ∑ _E : fixedBadPrimes.powerset, dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W :=
      Finset.sum_le_sum (fun E _ => hb E)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe,
        fixedBadPrimes_powerset_card]
      norm_num

end CanonicalQuadraticSieve

open scoped BigOperators Classical

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.GlobalEncoding
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem divisor_dyadic_sum_le (S T : Finset (Ideal O)) (N : ℝ)
    (f : Ideal O → Ideal O → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ j k : Fin (columnDyadicLength N + 1),
      (divisorDyadicBin S N j).Nonempty → (divisorDyadicBin T N k).Nonempty →
      (∑ D ∈ divisorDyadicBin S N j, ∑ E ∈ divisorDyadicBin T N k, f D E) ≤ C) :
    (∑ D ∈ S, ∑ E ∈ T, f D E) ≤ ((columnDyadicLength N + 1 : ℕ) : ℝ)^2 * C := by
  rw [sum_divisorDyadicRectangles S T N f]
  calc
    _ ≤ ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1), C := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      by_cases hS : (divisorDyadicBin S N j).Nonempty
      · by_cases hT : (divisorDyadicBin T N k).Nonempty
        · exact hb j k hS hT
        · simpa only [Finset.not_nonempty_iff_eq_empty.mp hT, Finset.sum_empty, Finset.sum_const_zero] using hC
      · simpa only [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.sum_empty] using hC
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_two]; ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma largePrincipalWindow_le (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) :
    largePrincipalWindow S T rows left right a b M P ≤
      principalCorrectionAt S T rows left right a b M := by
  classical
  unfold principalCorrectionAt
  rw [sum_two_subtype_pools S T (fun D E => ∑ i,
    (Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/((Ideal.absNorm D:ℝ)*(Ideal.absNorm E:ℝ)))*
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k‖)]
  unfold largePrincipalWindow
  apply Finset.sum_le_sum
  intro D _
  apply Finset.sum_le_sum
  intro E _
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> first | exact le_rfl | positivity

theorem HasSieveExponent.large_principal_window {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M V : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hM : 0 < M) (hV : 0 ≤ V) (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2*D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2*D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ D ∈ S, ∀ E ∈ T, ∀ i, P (D*E) i →
      Real.sqrt (M/B)*N ≤ (V/4)*(Ideal.absNorm (D*E):ℝ)) :
    largePrincipalWindow S T rows left right a b M P ≤
      2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (V+Real.sqrt M*B^(α-1/2)) := by
  classical
  by_cases hc : Real.sqrt (M/B)*N ≤ V*(D₁*D₂)
  · exact (largePrincipalWindow_le S T rows left right a b M P).trans
      (HasSieveExponent.large_principal_correction ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT
        rows left right hr hl hri hrows hleft hright a b hexp deltaLoss hδ hD₁N hD₂N V hc)
  · have hz : largePrincipalWindow S T rows left right a b M P = 0 := by
      unfold largePrincipalWindow
      apply Finset.sum_eq_zero
      intro D hD
      apply Finset.sum_eq_zero
      intro E hE
      apply Finset.sum_eq_zero
      intro i _
      have hn : ¬P (D*E) i := by
        intro hp
        apply hc
        have hlo := hP D hD E hE i hp
        have hhi : (Ideal.absNorm (D*E):ℝ) ≤ 4*(D₁*D₂) := by
          rw [map_mul, Nat.cast_mul]
          calc
            _ ≤ (2*D₁)*(2*D₂) := mul_le_mul (hS D hD).2 (hT E hE).2 (by positivity) (by linarith)
            _ = _ := by ring
        nlinarith
      simp only [hn, ite_false]
    rw [hz]
    have he := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity

theorem HasSieveExponent.large_principal_pool {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (B N M V : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hV : 0 ≤ V)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D:ℝ) ∧ (Ideal.absNorm D:ℝ) ≤ N)
    (hT : ∀ E ∈ T, 1 ≤ (Ideal.absNorm E:ℝ) ∧ (Ideal.absNorm E:ℝ) ≤ N)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ D ∈ S, ∀ E ∈ T, ∀ i, P (D*E) i →
      Real.sqrt (M/B)*N ≤ (V/4)*(Ideal.absNorm (D*E):ℝ)) :
    largePrincipalWindow S T rows left right a b M P ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (V+Real.sqrt M*B^(α-1/2))) := by
  classical
  apply divisor_dyadic_sum_le S T N _ _
  · have he := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity
  · intro j k hj hk
    exact hexp.large_principal_window deltaLoss hδ ε hε (divisorDyadicBin S N j) (divisorDyadicBin T N k)
      (divisorDyadicScale j.val) (divisorDyadicScale k.val) B N M V
      (divisorDyadicScale_ge_one _) (divisorDyadicScale_ge_one _) hB hN hM hV
      (divisorDyadicBin_scale_le S N hS j hj) (divisorDyadicBin_scale_le T N hT k hk)
      (divisorDyadicBin_bounds S N hS j) (divisorDyadicBin_bounds T N hT k)
      rows left right hr hl hri hrows hleft hright a b P
      (fun D hD E hE i hp => hP D (Finset.mem_filter.mp hD).1 E (Finset.mem_filter.mp hE).1 i hp)

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem finite_principal_triangle
    {m n p D : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype D]
    (muCoefficient : D → ℂ) (hμ : ∀ d, ‖muCoefficient d‖ ≤ 1) (A : m → n → p → D → ℂ) :
    ‖∑ i, ∑ j, ∑ k, ∑ d, muCoefficient d * A i j k d‖ ≤
      ∑ i, ∑ d, ‖∑ j, ∑ k, A i j k d‖ := by
  classical
  have he : (∑ i, ∑ j, ∑ k, ∑ d, muCoefficient d * A i j k d) =
      ∑ i, ∑ d, muCoefficient d * (∑ j, ∑ k, A i j k d) := by
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset p)) (t := (Finset.univ : Finset D)),
      Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset D))]
    simp only [Finset.mul_sum]
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hμ d)

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma largePrincipalProductAt_le_window (K S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T) :
    largePrincipalProductAt K rows left right a b M P ≤
      largePrincipalWindow S T rows left right a b M (fun d i => d ∈ K ∧ P d i) := by
  classical
  have hp (i : m) := originalColumnSum_divisor_rectangles K S T rows left right a b i
    hleft hright hS hT P
    (fun d i _ _ => ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ))
  apply (Finset.sum_le_sum (fun i _ => hp i)).trans_eq
  unfold largePrincipalWindow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E _
  apply Finset.sum_congr rfl
  intro i _
  by_cases hd : D*E ∈ K
  · by_cases hi : P (D*E) i
    · simp only [hd, hi, and_self, ite_true, map_mul, Nat.cast_mul]
      simp only [←Finset.sum_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/
          ((Ideal.absNorm D:ℝ)*(Ideal.absNorm E:ℝ)) by positivity)]
      ring
    · simp only [hd, hi, and_false, ite_true, ite_false]
  · simp only [hd, false_and, ite_false]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma principalDivisorCorrection_le_product (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hK : ∀ j k d, d ∣ left j*right k → d ∈ K) :
    ‖principalDivisorCorrection rows left right a b M P‖ ≤
      largePrincipalProductAt K rows left right a b M P := by
  classical
  let A : m → n → p → K → ℂ := fun i j k d => if P d.val i then
    if d.val ∣ left j*right k then originalTerm rows left right a b 1 1 i j k *
      ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d.val:ℝ):ℝ):ℂ) else 0 else 0
  have he : principalDivisorCorrection rows left right a b M P =
      ∑ i, ∑ j, ∑ k, ∑ d : K, (UniqueFactorizationMonoid.moebius d.val : ℂ)*A i j k d := by
    unfold principalDivisorCorrection
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [← divisorPool_filter K (left j*right k) (mul_ne_zero (hleft j) (hright k)) (hK j k),
      Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_coe_sort K (fun d => (UniqueFactorizationMonoid.moebius d:ℂ)*
      (if P d i then if d ∣ left j*right k then originalTerm rows left right a b 1 1 i j k *
        ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0 else 0))]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d ∣ left j*right k <;> by_cases hi : P d i <;>
      simp only [hd, hi, ite_true, ite_false, mul_zero] ; ring
  rw [he]
  apply (finite_principal_triangle (fun d : K => (UniqueFactorizationMonoid.moebius d.val:ℂ))
    (fun d => QuadraticInitialBound.norm_ideal_moebius_le_one d.val) A).trans_eq
  unfold largePrincipalProductAt
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_coe_sort K (fun d => ‖∑ j, ∑ k, if P d i then
    if d ∣ left j*right k then originalTerm rows left right a b 1 1 i j k *
      ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0 else 0‖)]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : P d i <;> simp only [hd, ite_true, ite_false, Finset.sum_const_zero, norm_zero]

theorem HasSieveExponent.principal_divisor_correction {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M V : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hV : 0 ≤ V)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ d i, P d i → Real.sqrt (M/B)*N ≤ (V/4)*(Ideal.absNorm d:ℝ)) :
    ‖principalDivisorCorrection rows left right a b M P‖ ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (V+Real.sqrt M*B^(α-1/2))) := by
  let S := columnDivisorPool left
  let T := columnDivisorPool right
  let pairCols : n × p → Ideal O := fun x => left x.1*right x.2
  let K := columnDivisorPool pairCols
  have hl0 : ∀ j, left j ≠ 0 := fun j => (hleft j).1.1
  have hr0 : ∀ k, right k ≠ 0 := fun k => (hright k).1.1
  have hp0 : ∀ x, pairCols x ≠ 0 := fun x => mul_ne_zero (hl0 x.1) (hr0 x.2)
  have hk : ∀ j k d, d ∣ left j*right k → d ∈ K :=
    fun j k d hd => mem_columnDivisorPool_of_dvd pairCols hp0 (j,k) d hd
  calc
    _ ≤ largePrincipalProductAt K rows left right a b M P :=
      principalDivisorCorrection_le_product K rows left right a b M P hl0 hr0 hk
    _ ≤ largePrincipalWindow S T rows left right a b M (fun d i => d ∈ K ∧ P d i) :=
      largePrincipalProductAt_le_window K S T rows left right a b M P hl0 hr0
        (mem_columnDivisorPool_of_dvd left hl0) (mem_columnDivisorPool_of_dvd right hr0)
    _ ≤ _ := hexp.large_principal_pool deltaLoss hδ ε hε S T B N M V hB hN hM hV
      (columnDivisorPool_norm_bounds left hl0 N (fun j => (hleft j).2))
      (columnDivisorPool_norm_bounds right hr0 N (fun k => (hright k).2))
      rows left right hr hl hri hrows hleft hright a b _
      (fun D _ E _ i hp => hP (D*E) i hp.2)

end CanonicalQuadraticSieve

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.MaskedPrincipalBounds
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic FourierBridge

lemma halfShellFactor_nonneg (N q : ℝ) : 0 ≤ halfShellFactor N q := by
  unfold halfShellFactor
  positivity

lemma halfShellFactor_le_one (N q : ℝ) (hq : 0 < q) (h : N/2 ≤ q) :
    halfShellFactor N q ≤ 1 := by
  unfold halfShellFactor
  exact (div_le_one (Real.sqrt_pos.mpr hq)).mpr (Real.sqrt_le_sqrt h)

lemma halfShellFactor_pair (M F N i j : ℝ) (hN : 0 < N) (hi : 0 < i) (hj : 0 < j)
    (hF : 0 < F) :
    (2*M/(F*N))*halfShellFactor N i*halfShellFactor N j =
      M/(Real.sqrt (i*j)*F) := by
  unfold halfShellFactor
  rw [Real.sqrt_mul hi.le]
  have hs := Real.sq_sqrt (show 0 ≤ N/2 by positivity)
  have hsi := (Real.sqrt_pos.mpr hi).ne'
  have hsj := (Real.sqrt_pos.mpr hj).ne'
  field_simp
  rw [hs]
  ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma originalTerm_real_scaling
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (u : n → ℝ) (v : p → ℝ)
    (D E : Ideal O) (i : m) (j : n) (k : p) :
    originalTerm rows left right (fun j => a j*(u j:ℂ)) (fun k => b k*(v k:ℂ)) D E i j k =
      originalTerm rows left right a b D E i j k * (u j:ℂ) * (v k:ℂ) := by
  unfold originalTerm
  by_cases hc : IsCoprime (left j) (right k) <;>
    by_cases hd : D ∣ left j <;> by_cases he : E ∣ right k <;>
    simp only [hc,hd,he,ite_true,ite_false,mul_zero,zero_mul,star_zero,star_mul,Complex.star_def,
      Complex.conj_ofReal] ; ring

theorem smallPrincipalCorrection_bound
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M F : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hN : 1 ≤ N)
    (hM : 0 < M) (hF : 0 < F)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2*D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2*D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) :
    smallPrincipalCorrection S T rows left right a b M F ≤
      (2*M/(F*N))*Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) := by
  have hN0 : 0 < N := by linarith
  let u := fun j => halfShellFactor N (Ideal.absNorm (left j) : ℝ)
  let v := fun k => halfShellFactor N (Ideal.absNorm (right k) : ℝ)
  let a' := fun j => a j*(u j:ℂ)
  let b' := fun k => b k*(v k:ℂ)
  have hu (j) : 0 ≤ u j ∧ u j ≤ 1 :=
    ⟨halfShellFactor_nonneg _ _,halfShellFactor_le_one _ _ (by linarith [(hleft j).2.1]) (hleft j).2.1⟩
  have hv (k) : 0 ≤ v k ∧ v k ≤ 1 :=
    ⟨halfShellFactor_nonneg _ _,halfShellFactor_le_one _ _ (by linarith [(hright k).2.1]) (hright k).2.1⟩
  have ha (j) : ‖a' j‖ ≤ ‖a j‖ := by
    simp only [a',norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hu j).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (hu j).2
  have hb (k) : ‖b' k‖ ≤ ‖b k‖ := by
    simp only [b',norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hv k).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (hv k).2
  have ht (D E : Ideal O) (i j k) :
      originalTerm rows left right a b D E i j k *
        ((M/(Real.sqrt ((Ideal.absNorm (left j) : ℝ)*(Ideal.absNorm (right k) : ℝ))*F) : ℝ) : ℂ) =
      ((2*M/(F*N):ℝ):ℂ)*originalTerm rows left right a' b' D E i j k := by
    have hid := halfShellFactor_pair M F N (Ideal.absNorm (left j) : ℝ) (Ideal.absNorm (right k) : ℝ)
      hN0 (by linarith [(hleft j).2.1]) (by linarith [(hright k).2.1]) hF
    rw [←hid, show originalTerm rows left right a' b' D E i j k =
      originalTerm rows left right a b D E i j k*(u j:ℂ)*(v k:ℂ) from
      originalTerm_real_scaling rows left right a b u v D E i j k]
    push_cast
    dsimp only [u,v]
    ring
  have hblock := canonical_original_divisor_block_phase_bound ε hε S T D₁ D₂ B N hD₁ hD₂ hN hS hT
    rows left right hr hl hri hrows (fun j => ⟨(hleft j).1,(hleft j).2.2⟩)
      (fun k => ⟨(hright k).1,(hright k).2.2⟩) a' b' (fun _ => 0) (fun _ => 0) 0
  simp only [zero_add,logPhase_zero,mul_one] at hblock
  have hcost := divisorBlockCost_mono_coefficients ε hε D₁ D₂ B N (by linarith) (by linarith) a' a b' b ha hb
  have heq : smallPrincipalCorrection S T rows left right a b M F =
      (2*M/(F*N))*(∑ D ∈ S, ∑ E ∈ T, ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a' b' D E i j k‖) := by
    unfold smallPrincipalCorrection
    simp_rw [ht,←Finset.mul_sum]
    simp only [norm_mul,Complex.norm_of_nonneg (show 0 ≤ 2*M/(F*N) by positivity)]
    simp_rw [←Finset.mul_sum]
  rw [heq]
  exact mul_le_mul_of_nonneg_left (hblock.trans (Real.sqrt_le_sqrt hcost)) (by positivity)

end

open ActualEisensteinCubic

theorem HasSieveExponent.small_principal_correction {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M F U : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hM : 0 < M) (hF : 0 < F) (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2*D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2*D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (hcut : D₁*D₂ ≤ U*(N*Real.sqrt (F/(M*B)))) :
    smallPrincipalCorrection S T rows left right a b M F ≤
      2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (M/F+U*Real.sqrt (M/F)*B^(α-1/2)) := by
  have hb := smallPrincipalCorrection_bound ε hε S T D₁ D₂ B N M F hD₁ hD₂ hN hM hF hS hT
    rows left right hr hl hri hrows hleft hright a b
  have hc := divisor_cost_with_constant hexp deltaLoss hδ ε hε B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N a b
  have he := divisorEnergyFactor_nonneg ε hε N a b
  have hC := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  calc
    _ ≤ (2*M/(F*N))*(divisorEnergyFactor ε hε N a b*
        (divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss*(N+B^α*(D₁*D₂)))) :=
      hb.trans (mul_le_mul_of_nonneg_left hc (by positivity))
    _ = (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss))*
        ((M/(F*N))*(N+B^α*(D₁*D₂))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (dual_middle_scale_shape M F B N (D₁*D₂) U α hM hF (by linarith) (by linarith) hcut)
      (by positivity)

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

theorem truncationError_symmetric_bound (m : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (_hinj : Function.Injective P) (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X₀ X T : ℝ),
        0 < X₀ → X₀ / 2 ≤ X → X ≤ 2 * X₀ → 4 ≤ T →
        ‖truncationError P S W X (X₀ / T) (T * X₀) (T ^ 4)‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ m := by
  obtain ⟨s, C, hC, hb⟩ := truncationError_bound (m + 3)
  refine ⟨s, C * 2 ^ (m + 10), by positivity, ?_⟩
  intro ι _ P _ hinj S W X₀ X T hX₀ hlo hhi hT
  obtain ⟨hX, hY, hYX, hXZ, hL⟩ := symmetric_truncation_scales X₀ X T hX₀ hlo hhi hT
  have hp := hb P hinj S W X (X₀ / T) (T * X₀) (T ^ 4) hX hY hYX hXZ hL
  have hs := symmetric_truncation_scalar_bound m X₀ X T hX₀ hlo hhi hT
  calc
    _ ≤ (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
        (((X₀ / T) / X) ^ (m + 3) + 1 / (1 + (T * X₀) / X) ^ (m + 3) +
          (X / (X₀ / T)) / ((min 1 (X / (T * X₀))) ^ 2 * (1 + X * T ^ 4 / (T * X₀)) ^ (m + 3))) := hp
    _ ≤ (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * (2 ^ (m + 10) / T ^ m) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

theorem primePool_symmetric_error_bound (m : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (G : Ideal O) (_hG : G ≠ 0)
        (W : 𝓢(ℝ, ℂ)) (X₀ X T : ℝ),
        0 < X₀ → X₀ / 2 ≤ X → X ≤ 2 * X₀ → 4 ≤ T →
        ‖truncationError (fun P : primePool {G} => P.val) Finset.univ W
          X (X₀ / T) (T * X₀) (T ^ 4)‖ ≤
          (supportConstant ε hε * (Ideal.absNorm G : ℝ) ^ ε) *
            (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ m := by
  obtain ⟨s, C, hC, hb⟩ := truncationError_symmetric_bound m
  refine ⟨s, C, hC, ?_⟩
  intro ε hε G hG W X₀ X T hX₀ hlo hhi hT
  have hh := hb (fun P : primePool {G} => P.val) Subtype.val_injective Finset.univ W
    X₀ X T hX₀ hlo hhi hT
  simp only [Finset.card_univ, Fintype.card_coe, primePool_singleton_eq_primeSupport] at hh
  apply hh.trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (support_card_bound ε hε G hG) (by positivity)) (by positivity)

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

theorem finite_ideal_family_card_bound {m : Type*} [Fintype m]
    (I : m → Ideal O) (hI : Function.Injective I) (B : ℝ) (hB : 1 ≤ B)
    (hzero : ∀ i, I i ≠ 0) (hNorm : ∀ i, (Ideal.absNorm (I i) : ℝ) ≤ B) :
    (Fintype.card m : ℝ) ≤ 128 * B := by
  classical
  have hb := DescentFiberCost.finite_ideal_count_real (Finset.univ.image I) B hB
    (by intro J hJ; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hJ; exact hzero i)
    (by intro J hJ; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hJ; exact hNorm i)
  simpa only [Finset.card_image_of_injective _ hI, Finset.card_univ] using hb

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.PrincipalNormalization
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem signedProductDivisorSum_le_rectangles (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (H : Ideal O → m → n → p → ℂ)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T) :
    ‖signedProductDivisorSum rows left right a b P H‖ ≤
      correctionRectangleMajorant S T rows left right a b P H := by
  classical
  let pairCols : n × p → Ideal O := fun x => left x.1*right x.2
  let K := columnDivisorPool pairCols
  have hpair : ∀ x, pairCols x ≠ 0 := fun x => mul_ne_zero (hleft x.1) (hright x.2)
  have hK : ∀ j k d, d ∣ left j*right k → d ∈ K :=
    fun j k d hd => mem_columnDivisorPool_of_dvd pairCols hpair (j,k) d hd
  let A : m → n → p → K → ℂ := fun i j k d => if P d.val i then
    if d.val ∣ left j*right k then originalTerm rows left right a b 1 1 i j k * H d.val i j k else 0 else 0
  have he : signedProductDivisorSum rows left right a b P H =
      ∑ i, ∑ j, ∑ k, ∑ d : K, (UniqueFactorizationMonoid.moebius d.val:ℂ)*A i j k d := by
    unfold signedProductDivisorSum
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [← divisorPool_filter K (left j*right k) (mul_ne_zero (hleft j) (hright k)) (hK j k),
      Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_coe_sort K (fun d => (UniqueFactorizationMonoid.moebius d:ℂ)*
      (if P d i then if d ∣ left j*right k then originalTerm rows left right a b 1 1 i j k * H d i j k else 0 else 0))]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d ∣ left j*right k <;> by_cases hi : P d i <;>
      simp only [hd, hi, ite_true, ite_false, mul_zero] ; ring
  rw [he]
  apply (finite_principal_triangle (fun d : K => (UniqueFactorizationMonoid.moebius d.val:ℂ))
    (fun d => QuadraticInitialBound.norm_ideal_moebius_le_one d.val) A).trans
  have hp (i : m) := originalColumnSum_divisor_rectangles K S T rows left right a b i
    hleft hright hS hT P H
  have hi (i : m) : (∑ d : K, ‖∑ j, ∑ k, A i j k d‖) =
      ∑ d ∈ K, if P d i then ‖∑ j, ∑ k, if d ∣ left j*right k then
        originalTerm rows left right a b 1 1 i j k * H d i j k else 0‖ else 0 := by
    rw [Finset.sum_coe_sort K (fun d => ‖∑ j, ∑ k, if P d i then if d ∣ left j*right k then
      originalTerm rows left right a b 1 1 i j k * H d i j k else 0 else 0‖)]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : P d i <;> simp only [hd, ite_true, ite_false, Finset.sum_const_zero, norm_zero]
  simp_rw [hi]
  apply (Finset.sum_le_sum (fun i _ => hp i)).trans
  unfold correctionRectangleMajorant
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro D _
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro E _
  apply Finset.sum_le_sum
  intro i _
  by_cases hd : D*E ∈ K
  · simp only [hd, ite_true]
    exact le_rfl
  · simp only [hd, ite_false]
    positivity

theorem HasSieveExponent.small_principal_window {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M F U : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U) (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D:ℝ) ∧ (Ideal.absNorm D:ℝ) ≤ 2*D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E:ℝ) ∧ (Ideal.absNorm E:ℝ) ≤ 2*D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j):ℝ) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k):ℝ) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ D ∈ S, ∀ E ∈ T, ∀ i, P (D*E) i → (Ideal.absNorm (D*E):ℝ) ≤
      U*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))) :
    correctionRectangleMajorant S T rows left right a b P
      (fun _ _ j k => ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ)) ≤
      2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (M/F+(2*U)*Real.sqrt (M/F)*B^(α-1/2)) := by
  classical
  by_cases hc : D₁*D₂ ≤ (2*U)*(N*Real.sqrt (F/(M*B)))
  · apply le_trans (b := smallPrincipalCorrection S T rows left right a b M F)
    · unfold correctionRectangleMajorant smallPrincipalCorrection
      apply Finset.sum_le_sum
      intro D _
      apply Finset.sum_le_sum
      intro E _
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> first | exact le_rfl | positivity
    · exact hexp.small_principal_correction deltaLoss hδ ε hε S T D₁ D₂ B N M F (2*U)
        hD₁ hD₂ hB hN hM hF hD₁N hD₂N hS hT rows left right hr hl hri
        (fun i => ⟨(hrows i).1,(hrows i).2.2⟩) hleft hright a b hc
  · have hz : correctionRectangleMajorant S T rows left right a b P
        (fun _ _ j k => ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ)) = 0 := by
      unfold correctionRectangleMajorant
      apply Finset.sum_eq_zero
      intro D hD
      apply Finset.sum_eq_zero
      intro E hE
      apply Finset.sum_eq_zero
      intro i _
      have hn : ¬P (D*E) i := by
        intro hp
        apply hc
        apply dual_middle_rectangle_upper M F B (Ideal.absNorm (rows i)) N D₁ D₂
          (Ideal.absNorm D) (Ideal.absNorm E) U hM hF (by linarith) (hrows i).2.1
          (by linarith) hU (by linarith) (by linarith) (hS D hD).1 (hT E hE).1
        simpa only [map_mul,Nat.cast_mul] using hP D hD E hE i hp
      simp only [hn,ite_false]
    rw [hz]
    have he := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity

theorem HasSieveExponent.small_principal_divisor_sum {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j):ℝ) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k):ℝ) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ d i, P d i → (Ideal.absNorm d:ℝ) ≤ U*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))) :
    ‖signedProductDivisorSum rows left right a b P
      (fun _ _ j k => ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ))‖ ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (M/F+(2*U)*Real.sqrt (M/F)*B^(α-1/2))) := by
  classical
  let S := columnDivisorPool left
  let T := columnDivisorPool right
  have hl0 : ∀ j, left j ≠ 0 := fun j => (hleft j).1.1
  have hr0 : ∀ k, right k ≠ 0 := fun k => (hright k).1.1
  have hS := columnDivisorPool_norm_bounds left hl0 N (fun j => (hleft j).2.2)
  have hT := columnDivisorPool_norm_bounds right hr0 N (fun k => (hright k).2.2)
  apply (signedProductDivisorSum_le_rectangles S T rows left right a b P _ hl0 hr0
    (mem_columnDivisorPool_of_dvd left hl0) (mem_columnDivisorPool_of_dvd right hr0)).trans
  apply divisor_dyadic_sum_le S T N _ _
  · have he := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity
  · intro j k hj hk
    exact hexp.small_principal_window deltaLoss hδ ε hε (divisorDyadicBin S N j) (divisorDyadicBin T N k)
      (divisorDyadicScale j.val) (divisorDyadicScale k.val) B N M F U
      (divisorDyadicScale_ge_one _) (divisorDyadicScale_ge_one _) hB hN hM hF hU
      (divisorDyadicBin_scale_le S N hS j hj) (divisorDyadicBin_scale_le T N hT k hk)
      (divisorDyadicBin_bounds S N hS j) (divisorDyadicBin_bounds T N hT k)
      rows left right hr hl hri hrows hleft hright a b P (fun D _ E _ i hp => hP (D*E) i hp)

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

lemma dual_large_cut_lower (M F B b N T d : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 < B) (hb : 0 < b) (hbB : b ≤ B)
    (hN : 0 < N) (hT : 0 < T) (hd : T*(N*Real.sqrt (F/(M*b))) ≤ d) :
    Real.sqrt ((M/F)/B)*N ≤ ((4*M/(F*T))/4)*d := by
  have hs : Real.sqrt (F/(M*B)) ≤ Real.sqrt (F/(M*b)) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hF.le (by positivity) (mul_le_mul_of_nonneg_left hbB hM.le))
  have hnd : N*Real.sqrt (F/(M*B)) ≤ d/T := by
    apply (le_div_iff₀ hT).mpr
    calc
      _ = T*(N*Real.sqrt (F/(M*B))) := by ring
      _ ≤ T*(N*Real.sqrt (F/(M*b))) := by gcongr
      _ ≤ d := hd
  rw [dual_middle_scale_identity M F B N hM hF hB hN]
  calc
    _ ≤ ((M/(F*N))*(d/T))*N := by gcongr
    _ = _ := by field_simp

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem HasSieveExponent.dual_large_principal_sum {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F T : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hT : 0 < T)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (Z : m → ℝ)
    (hZ : ∀ i, T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ)))) ≤ Z i) :
    ‖principalDivisorCorrection rows left right a b (M/F) (fun d i => Z i < (Ideal.absNorm d:ℝ))‖ ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (4*M/(F*T)+Real.sqrt (M/F)*B^(α-1/2))) := by
  apply hexp.principal_divisor_correction deltaLoss hδ ε hε B N (M/F) (4*M/(F*T)) hB hN (by positivity) (by positivity)
    rows left right hr hl hri hrows hleft hright a b
  intro d i hd
  exact dual_large_cut_lower M F B (Ideal.absNorm (rows i)) N T (Ideal.absNorm d) hM hF (by linarith)
    (by linarith [(hrows i).2.1]) (hrows i).2.2 (by linarith) hT ((hZ i).trans hd.le)

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.LogarithmicSectors
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

theorem sqrt_product_column_shell (N i j : ℝ) (hN : 0 < N)
    (hi : N / 2 ≤ i ∧ i ≤ N) (hj : N / 2 ≤ j ∧ j ≤ N) :
    N / 2 ≤ Real.sqrt (i * j) ∧ Real.sqrt (i * j) ≤ N := by
  have hi0 : 0 < i := by linarith
  have hj0 : 0 < j := by linarith
  have hlo : (N / 2) ^ 2 ≤ i * j := by
    simpa only [pow_two] using mul_le_mul hi.1 hj.1 (by linarith : 0 ≤ N / 2) hi0.le
  have hhi : i * j ≤ N ^ 2 := by
    simpa only [pow_two] using mul_le_mul hi.2 hj.2 hj0.le hN.le
  have hs := Real.sq_sqrt (mul_pos hi0 hj0).le
  have hp := Real.sqrt_nonneg (i * j)
  constructor <;> nlinarith

theorem dual_truncation_reference_bounds (M F b N i j : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hb : 0 < b) (hN : 0 < N)
    (hi : N / 2 ≤ i ∧ i ≤ N) (hj : N / 2 ≤ j ∧ j ≤ N) :
    0 < N * Real.sqrt (F / (M * b)) ∧
      (N * Real.sqrt (F / (M * b))) / 2 ≤ Real.sqrt (F * i * j / (M * b)) ∧
      Real.sqrt (F * i * j / (M * b)) ≤ 2 * (N * Real.sqrt (F / (M * b))) := by
  have hr : 0 < Real.sqrt (F / (M * b)) := Real.sqrt_pos.mpr (by positivity)
  have he : Real.sqrt (F * i * j / (M * b)) = Real.sqrt (F / (M * b)) * Real.sqrt (i * j) := by
    rw [← Real.sqrt_mul (show 0 ≤ F / (M * b) by positivity)]
    congr 1
    ring
  obtain ⟨hlo, hhi⟩ := sqrt_product_column_shell N i j hN hi hj
  refine ⟨mul_pos hN hr, ?_, ?_⟩
  · rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hlo hr.le]
  · rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hhi hr.le, mul_pos hN hr]

theorem dual_truncation_prefactor_bound (M F N i j : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hN : 0 < N)
    (hi : N / 2 ≤ i ∧ i ≤ N) (hj : N / 2 ≤ j ∧ j ≤ N) :
    M / (Real.sqrt (i * j) * F) ≤ 2 * M / (F * N) := by
  obtain ⟨hlo, _⟩ := sqrt_product_column_shell N i j hN hi hj
  calc
    _ ≤ M / ((N / 2) * F) := div_le_div_of_nonneg_left hM.le (by positivity)
      (mul_le_mul_of_nonneg_right hlo hF.le)
    _ = _ := by field_simp

variable {m n : Type*} [Fintype m] [Fintype n]

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.PrincipalMajorants
namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

section

open scoped BigOperators Classical SchwartzMap

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open IdealMobiusDivisorSum

lemma smallPrincipalMajorant_nonneg {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U : ℝ) (a : n → ℂ) (b : p → ℂ)
    (hB : 0 ≤ B) (hN : 0 ≤ N) (hM : 0 ≤ M) (hF : 0 ≤ F) (hU : 0 ≤ U) :
    0 ≤ smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b := by
  have he := divisorEnergyFactor_nonneg ε hε N a b
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  unfold smallPrincipalMajorant
  positivity

lemma smallPrincipalMajorant_mono {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B' B N M F U : ℝ) (a a' : n → ℂ) (b b' : p → ℂ)
    (hB' : 0 ≤ B') (hB : B' ≤ B) (hN : 0 ≤ N) (hM : 0 ≤ M) (hF : 0 ≤ F) (hU : 0 ≤ U)
    (ha : ∀ j, ‖a' j‖ ≤ ‖a j‖) (hb : ∀ k, ‖b' k‖ ≤ ‖b k‖) :
    smallPrincipalMajorant hexp deltaLoss hδ ε hε B' N M F U a' b' ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b := by
  have he := divisorEnergyFactor_mono_coefficients ε hε N a a' b b' ha hb
  have he0 := divisorEnergyFactor_nonneg ε hε N a' b'
  have he1 := divisorEnergyFactor_nonneg ε hε N a b
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  have ha0 : 0 ≤ α-1/2 := by linarith
  have hB0 : 0 ≤ B := hB'.trans hB
  unfold smallPrincipalMajorant
  gcongr

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma unrestrictedSmallPrincipalSum_sector
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop)
    (hrows : ∀ i, Squarefree (rows i)) (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) :
    unrestrictedSmallPrincipalSum rows left right a b M F P =
      signedProductDivisorSum (fun i => goodSquarefreePart (rows i)) left right
        (fun j => a j*quadraticRow (left j) (idealGenerator (sectorBadIdeal E)))
        (fun k => b k*quadraticRow (right k) (idealGenerator (sectorBadIdeal E))) P
        (fun _ _ j k => ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ)) := by
  unfold unrestrictedSmallPrincipalSum signedProductDivisorSum
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [unrestrictedPairTerm_sector rows left right a b hrows hleft hright hray E hE i j k]

theorem HasSieveExponent.small_principal_sector {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Squarefree (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j):ℝ) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k):ℝ) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ d i, P d i → (Ideal.absNorm d:ℝ) ≤ U*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ)))))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) :
    ‖unrestrictedSmallPrincipalSum rows left right a b M F P‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b := by
  classical
  cases isEmpty_or_nonempty m with
  | inl hempty =>
    let := hempty
    simp only [unrestrictedSmallPrincipalSum, Finset.univ_eq_empty, Finset.sum_empty, norm_zero]
    exact smallPrincipalMajorant_nonneg hexp deltaLoss hδ ε hε B N M F U a b (by linarith) (by linarith) hM.le hF.le hU
  | inr hnonempty =>
    let := hnonempty
    let i₀ : m := Classical.choice hnonempty
    let Q : ℝ := Ideal.absNorm (sectorBadIdeal E)
    let good := fun i => goodSquarefreePart (rows i)
    let a' := fun j => a j*quadraticRow (left j) (idealGenerator (sectorBadIdeal E))
    let b' := fun k => b k*quadraticRow (right k) (idealGenerator (sectorBadIdeal E))
    have hQnz := sectorBadIdeal_ne_zero_of_row (rows i₀) (hrows i₀).1 E (hE i₀)
    have hQ : 1 ≤ Q := by
      dsimp only [Q]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun h => hQnz (Ideal.absNorm_eq_zero_iff.mp h)))
    have hQp : 0 < Q := by linarith
    have hn (i : m) : (Ideal.absNorm (rows i):ℝ) = Q*(Ideal.absNorm (good i):ℝ) := by
      have hi := congrArg (fun I : Ideal O => (Ideal.absNorm I:ℝ))
        (sector_bad_good_product (rows i) (hrows i).1 E (hE i))
      simpa only [map_mul,Nat.cast_mul] using hi.symm
    have hgr : Function.Injective good := by
      intro i k h
      exact hr (goodSquarefreePart_injective_on_sector _ _ (hrows i).1 (hrows k).1
        ((hE i).trans (hE k).symm) h)
    have hg (i : m) : Admissible (good i) ∧ (B/Q)/2 ≤ (Ideal.absNorm (good i):ℝ) ∧
        (Ideal.absNorm (good i):ℝ) ≤ B/Q := by
      refine ⟨goodSquarefreePart_admissible _, ?_, ?_⟩
      · rw [show B/Q/2 = (B/2)/Q by ring]
        apply (div_le_iff₀ hQp).2
        have hx := (hrows i).2.1
        rw [hn i] at hx
        nlinarith
      · exact (le_div_iff₀ hQp).2 (by simpa only [mul_comm] using (hn i).symm.trans_le (hrows i).2.2)
    have hBQ : 1 ≤ B/Q := by
      have hh : 1 ≤ (Ideal.absNorm (good i₀):ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun h => (hg i₀).1.1 (Ideal.absNorm_eq_zero_iff.mp h)))
      exact hh.trans (hg i₀).2.2
    have hPg (d : Ideal O) (i : m) (hp : P d i) : (Ideal.absNorm d:ℝ) ≤
        U*(N*Real.sqrt (F/(M*(Ideal.absNorm (good i):ℝ)))) := by
      apply (hP d i hp).trans
      have hgoodpos : 0 < (Ideal.absNorm (good i):ℝ) := by
        exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => (hg i).1.1 (Ideal.absNorm_eq_zero_iff.mp h))
      have hng : (Ideal.absNorm (good i):ℝ) ≤ (Ideal.absNorm (rows i):ℝ) :=
        Nat.cast_le.mpr (goodSquarefreePart_norm_le (rows i) (hrows i).1)
      gcongr
    rw [unrestrictedSmallPrincipalSum_sector rows left right a b M F P
      (fun i => (hrows i).1) (fun j => (hleft j).1) (fun k => (hright k).1) hray E hE]
    have hbnd := hexp.small_principal_divisor_sum deltaLoss hδ ε hε (B/Q) N M F U hBQ hN hM hF hU
      good left right hgr hl hri hg hleft hright a' b' P hPg
    change ‖signedProductDivisorSum good left right a' b' P _‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b
    apply hbnd.trans
    apply smallPrincipalMajorant_mono hexp hα deltaLoss hδ ε hε (B/Q) B N M F U a a' b b'
      (by positivity) (div_le_self (by linarith) hQ) (by linarith) hM.le hF.le hU
    · intro j
      dsimp only [a']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)
    · intro k
      dsimp only [b']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)

theorem HasSieveExponent.unrestricted_small_principal_sum {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Squarefree (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j):ℝ) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k):ℝ) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ d i, P d i → (Ideal.absNorm d:ℝ) ≤ U*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))) :
    ‖unrestrictedSmallPrincipalSum rows left right a b M F P‖ ≤
      4*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b := by
  classical
  let σ := fun i => badPrimeSector (rows i)
  have hs : unrestrictedSmallPrincipalSum rows left right a b M F P =
      ∑ E : fixedBadPrimes.powerset, unrestrictedSmallPrincipalSum
        (fun i : {i // σ i = E} => rows i.val) left right a b M F (fun d i => P d i.val) := by
    unfold unrestrictedSmallPrincipalSum
    exact (Fintype.sum_fiberwise σ _).symm
  have hb (E : fixedBadPrimes.powerset) :
      ‖unrestrictedSmallPrincipalSum (fun i : {i // σ i = E} => rows i.val)
        left right a b M F (fun d i => P d i.val)‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b :=
    hexp.small_principal_sector hα deltaLoss hδ ε hε B N M F U hB hN hM hF hU
      (fun i : {i // σ i = E} => rows i.val) left right (fun i k h => Subtype.ext (hr h)) hl hri
      (fun i => hrows i.val) hleft hright hray a b (fun d i => P d i.val) (fun d i => hP d i.val)
      E (fun i => i.property)
  rw [hs]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _E : fixedBadPrimes.powerset, smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b :=
      Finset.sum_le_sum (fun E _ => hb E)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe, fixedBadPrimes_powerset_card]
      norm_num

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open IdealMobiusDivisorSum

lemma smallPrincipalMajorant_bad_scale {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U Q : ℝ) (a a' : n → ℂ) (b b' : p → ℂ)
    (hB : 0 ≤ B) (hN : 0 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U) (hQ : 1 ≤ Q)
    (ha : ∀ j, ‖a' j‖ ≤ ‖a j‖) (hb : ∀ k, ‖b' k‖ ≤ ‖b k‖) :
    (1/Q)*smallPrincipalMajorant hexp deltaLoss hδ ε hε (B/Q) N (M*Q) F U a' b' ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b := by
  have hQp : 0 < Q := by linarith
  have he := divisorEnergyFactor_mono_coefficients ε hε N a a' b b' ha hb
  have hp : ((B/Q)*N)^deltaLoss ≤ (B*N)^deltaLoss := by
    apply Real.rpow_le_rpow (by positivity) _ hδ.le
    exact mul_le_mul_of_nonneg_right (div_le_self hB hQ) hN
  have hs := dual_bad_sector_scale M F B Q U α hM hF hB hQ hU hα
  have he0 := divisorEnergyFactor_nonneg ε hε N a' b'
  have he1 := divisorEnergyFactor_nonneg ε hε N a b
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  unfold smallPrincipalMajorant
  calc
    _ = ((columnDyadicLength N+1:ℕ):ℝ)^2 *
      (2*divisorEnergyFactor ε hε N a' b'*(divisorExponentConstant hexp deltaLoss hδ*((B/Q)*N)^deltaLoss)*
        ((1/Q)*(M*Q/F+(2*U)*Real.sqrt (M*Q/F)*(B/Q)^(α-1/2)))) := by ring
    _ ≤ _ := by gcongr

lemma sqrt_sector_scale (M F Q b : ℝ) (hM : 0 < M) (hF : 0 < F) (hQ : 0 < Q) (hb : 0 < b) :
    Real.sqrt ((M/F)/(Q*b)) = (1/Q)*Real.sqrt (((M*Q)/F)/b) := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt (show 0 ≤ (M/F)/(Q*b) by positivity),
    Real.sq_sqrt (show 0 ≤ ((M*Q)/F)/b by positivity)]
  field_simp

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma unrestrictedLargePrincipalSum_sector
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Z : m → ℝ) (hM : 0 < M) (hF : 0 < F)
    (hrows : ∀ i, Squarefree (rows i)) (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) (hQ : sectorBadIdeal E ≠ 0) :
    unrestrictedLargePrincipalSum rows left right a b M F Z =
      ((1/(Ideal.absNorm (sectorBadIdeal E):ℝ):ℝ):ℂ)*
        principalDivisorCorrection (fun i => goodSquarefreePart (rows i)) left right
          (fun j => a j*quadraticRow (left j) (idealGenerator (sectorBadIdeal E)))
          (fun k => b k*quadraticRow (right k) (idealGenerator (sectorBadIdeal E)))
          ((M*(Ideal.absNorm (sectorBadIdeal E):ℝ))/F) (fun d i => Z i < (Ideal.absNorm d:ℝ)) := by
  classical
  have hQp : 0 < (Ideal.absNorm (sectorBadIdeal E):ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hQ (Ideal.absNorm_eq_zero_iff.mp h))
  unfold unrestrictedLargePrincipalSum principalDivisorCorrection
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [unrestrictedPairTerm_sector rows left right a b hrows hleft hright hray E hE i j k]
  have hn : (Ideal.absNorm (rows i):ℝ) =
      (Ideal.absNorm (sectorBadIdeal E):ℝ)*(Ideal.absNorm (goodSquarefreePart (rows i)):ℝ) := by
    have hi := congrArg (fun I : Ideal O => (Ideal.absNorm I:ℝ))
      (sector_bad_good_product (rows i) (hrows i) E (hE i))
    simpa only [map_mul,Nat.cast_mul] using hi.symm
  have hgpos : 0 < (Ideal.absNorm (goodSquarefreePart (rows i)):ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h =>
      (goodSquarefreePart_admissible (rows i)).1 (Ideal.absNorm_eq_zero_iff.mp h))
  rw [hn,sqrt_sector_scale M F _ _ hM hF hQp hgpos]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : Z i < (Ideal.absNorm d:ℝ)
  · simp only [hd,ite_true,Complex.ofReal_div,Complex.ofReal_mul]
    ring
  · simp only [hd,ite_false,mul_zero]

theorem HasSieveExponent.large_principal_sector {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F T : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hT : 4 ≤ T)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Squarefree (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (a : n → ℂ) (b : p → ℂ) (Z : m → ℝ)
    (hZ : ∀ i, T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ)))) ≤ Z i)
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) :
    ‖unrestrictedLargePrincipalSum rows left right a b M F Z‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a b := by
  classical
  cases isEmpty_or_nonempty m with
  | inl hempty =>
    let := hempty
    simp only [unrestrictedLargePrincipalSum,Finset.univ_eq_empty,Finset.sum_empty,norm_zero]
    exact smallPrincipalMajorant_nonneg hexp deltaLoss hδ ε hε B N M F (1/2) a b
      (by linarith) (by linarith) hM.le hF.le (by norm_num)
  | inr hnonempty =>
    let := hnonempty
    let i₀ : m := Classical.choice hnonempty
    let Q : ℝ := Ideal.absNorm (sectorBadIdeal E)
    let good := fun i => goodSquarefreePart (rows i)
    let a' := fun j => a j*quadraticRow (left j) (idealGenerator (sectorBadIdeal E))
    let b' := fun k => b k*quadraticRow (right k) (idealGenerator (sectorBadIdeal E))
    have hQnz := sectorBadIdeal_ne_zero_of_row (rows i₀) (hrows i₀).1 E (hE i₀)
    have hQ : 1 ≤ Q := by
      dsimp only [Q]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun h => hQnz (Ideal.absNorm_eq_zero_iff.mp h)))
    have hQp : 0 < Q := by linarith
    have hn (i : m) : (Ideal.absNorm (rows i):ℝ) = Q*(Ideal.absNorm (good i):ℝ) := by
      have hi := congrArg (fun I : Ideal O => (Ideal.absNorm I:ℝ))
        (sector_bad_good_product (rows i) (hrows i).1 E (hE i))
      simpa only [map_mul,Nat.cast_mul] using hi.symm
    have hgr : Function.Injective good := by
      intro i k h
      exact hr (goodSquarefreePart_injective_on_sector _ _ (hrows i).1 (hrows k).1
        ((hE i).trans (hE k).symm) h)
    have hg (i : m) : Admissible (good i) ∧ (B/Q)/2 ≤ (Ideal.absNorm (good i):ℝ) ∧
        (Ideal.absNorm (good i):ℝ) ≤ B/Q := by
      refine ⟨goodSquarefreePart_admissible _, ?_, ?_⟩
      · rw [show B/Q/2 = (B/2)/Q by ring]
        apply (div_le_iff₀ hQp).2
        have hx := (hrows i).2.1
        rw [hn i] at hx
        nlinarith
      · exact (le_div_iff₀ hQp).2 (by simpa only [mul_comm] using (hn i).symm.trans_le (hrows i).2.2)
    have hBQ : 1 ≤ B/Q := by
      have hh : 1 ≤ (Ideal.absNorm (good i₀):ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun h => (hg i₀).1.1 (Ideal.absNorm_eq_zero_iff.mp h)))
      exact hh.trans (hg i₀).2.2
    have hZg (i : m) : T*(N*Real.sqrt (F/((M*Q)*(Ideal.absNorm (good i):ℝ)))) ≤ Z i := by
      simpa only [hn i,mul_assoc] using hZ i
    have hbnd := hexp.dual_large_principal_sum deltaLoss hδ ε hε (B/Q) N (M*Q) F T hBQ hN
      (by positivity) hF (by linarith) good left right hgr hl hri hg hleft hright a' b' Z hZg
    have hmajor : ‖principalDivisorCorrection good left right a' b' ((M*Q)/F)
        (fun d i => Z i < (Ideal.absNorm d:ℝ))‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε (B/Q) N (M*Q) F (1/2) a' b' := by
      apply hbnd.trans
      have ht : 4/T ≤ 1 := (div_le_one (by linarith : 0<T)).mpr hT
      have hlead : 4*(M*Q)/(F*T) ≤ (M*Q)/F := by
        calc
          _ = ((M*Q)/F)*(4/T) := by ring
          _ ≤ _ := mul_le_of_le_one_right (by positivity) ht
      have he := divisorEnergyFactor_nonneg ε hε N a' b'
      have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
      unfold smallPrincipalMajorant
      norm_num only [show (2:ℝ)*(1/2)=1 by norm_num,one_mul]
      gcongr
    have htr := unrestrictedLargePrincipalSum_sector rows left right a b M F Z hM hF
      (fun i => (hrows i).1) (fun j => (hleft j).1) (fun k => (hright k).1) hray E hE hQnz
    change unrestrictedLargePrincipalSum rows left right a b M F Z =
      ((1/Q:ℝ):ℂ)*principalDivisorCorrection good left right a' b' ((M*Q)/F)
        (fun d i => Z i < (Ideal.absNorm d:ℝ)) at htr
    rw [htr,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤1/Q)]
    apply (mul_le_mul_of_nonneg_left hmajor (by positivity)).trans
    apply smallPrincipalMajorant_bad_scale hexp hα deltaLoss hδ ε hε B N M F (1/2) Q a a' b b'
      (by linarith) (by linarith) hM hF (by norm_num) hQ
    · intro j
      dsimp only [a']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)
    · intro k
      dsimp only [b']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)

theorem HasSieveExponent.unrestricted_large_principal_sum {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F T : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hT : 4 ≤ T)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Squarefree (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (a : n → ℂ) (b : p → ℂ) (Z : m → ℝ)
    (hZ : ∀ i, T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ)))) ≤ Z i) :
    ‖unrestrictedLargePrincipalSum rows left right a b M F Z‖ ≤
      4*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a b := by
  classical
  let σ := fun i => badPrimeSector (rows i)
  have hs : unrestrictedLargePrincipalSum rows left right a b M F Z =
      ∑ E : fixedBadPrimes.powerset, unrestrictedLargePrincipalSum
        (fun i : {i // σ i = E} => rows i.val) left right a b M F (fun i => Z i.val) := by
    unfold unrestrictedLargePrincipalSum
    exact (Fintype.sum_fiberwise σ _).symm
  have hb (E : fixedBadPrimes.powerset) :
      ‖unrestrictedLargePrincipalSum (fun i : {i // σ i = E} => rows i.val)
        left right a b M F (fun i => Z i.val)‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a b :=
    hexp.large_principal_sector hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT
      (fun i : {i // σ i = E} => rows i.val) left right (fun i k h => Subtype.ext (hr h)) hl hri
      (fun i => hrows i.val) hleft hright hray a b (fun i => Z i.val) (fun i => hZ i.val)
      E (fun i => i.property)
  rw [hs]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _E : fixedBadPrimes.powerset, smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a b :=
      Finset.sum_le_sum (fun E _ => hb E)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_coe,fixedBadPrimes_powerset_card]
      norm_num

end

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

lemma unrestrictedPairTerm_norm_le {m n p : Type}
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (i : m) (j : n) (k : p) :
    ‖unrestrictedPairTerm rows left right a b i j k‖ ≤ ‖a j‖*‖b k‖ := by
  classical
  unfold unrestrictedPairTerm
  split_ifs with hc
  · simp only [unrestrictedPairCharacter,norm_mul,norm_star]
    calc
      _ ≤ (‖a j‖*‖b k‖)*(1*1) := mul_le_mul_of_nonneg_left
        (mul_le_mul (quadraticRow_norm_le_one _ _) (quadraticRow_norm_le_one _ _)
          (norm_nonneg _) (by norm_num)) (by positivity)
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

theorem unrestricted_pair_error_energy {m n : Type} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ)
    (E : ℝ) (hE : 0 ≤ E) (error : m → n → n → ℂ)
    (herr : ∀ i j k, ‖error i j k‖ ≤ E) :
    ‖∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows cols cols a a i j k * error i j k‖ ≤
      Fintype.card m * Fintype.card n * E * ∑ j, ‖a j‖ ^ 2 := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j : n => ‖a j‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hcs
  have hs : (∑ j, ∑ k, ‖a j‖ * ‖a k‖ * E) = (∑ j, ‖a j‖) ^ 2 * E := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  calc
    _ ≤ ∑ i, ∑ j, ∑ k, ‖unrestrictedPairTerm rows cols cols a a i j k * error i j k‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun j hj => norm_sum_le _ _)
    _ ≤ ∑ _i : m, ∑ j, ∑ k, ‖a j‖ * ‖a k‖ * E := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul]
      exact mul_le_mul (unrestrictedPairTerm_norm_le rows cols cols a a i j k) (herr i j k)
        (norm_nonneg _) (by positivity)
    _ = (Fintype.card m : ℝ) * ((∑ j, ‖a j‖) ^ 2 * E) := by
      simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Fintype.card m : ℝ) * (((∑ j, ‖a j‖ ^ 2) * Fintype.card n) * E) := by gcongr
    _ = _ := by ring

theorem unrestricted_pair_error_ideal_bound {m n : Type} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (hr : Function.Injective rows) (hc : Function.Injective cols)
    (B N : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (hcols : ∀ j, cols j ≠ 0 ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (a : n → ℂ) (E : ℝ) (hE : 0 ≤ E) (error : m → n → n → ℂ)
    (herr : ∀ i j k, ‖error i j k‖ ≤ E) :
    ‖∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows cols cols a a i j k * error i j k‖ ≤
      16384 * B * N * E * ∑ j, ‖a j‖ ^ 2 := by
  have hrc := finite_ideal_family_card_bound rows hr B hB (fun i => (hrows i).1) (fun i => (hrows i).2)
  have hcc := finite_ideal_family_card_bound cols hc N hN (fun j => (hcols j).1) (fun j => (hcols j).2)
  apply (unrestricted_pair_error_energy rows cols a E hE error herr).trans
  calc
    _ ≤ (128 * B) * (128 * N) * E * ∑ j, ‖a j‖ ^ 2 := by gcongr
    _ = _ := by ring

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.RetainedDualBounds
namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

section

open scoped BigOperators Classical SchwartzMap

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem principalTruncation_scaled (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (c X Z : ℝ) :
    (c:ℂ)*principalTruncation (fun P : primePool {G} => P.val) Finset.univ W X Z =
      ((c*X:ℝ):ℂ)*paperRadialFourier W 0*primePoolDensity G -
      paperRadialFourier W 0 * (∑ d ∈ idealDivisors G, if Z < (Ideal.absNorm d:ℝ) then
        (UniqueFactorizationMonoid.moebius d:ℂ)*(((c*X)/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0) -
      W 0 * (∑ d ∈ idealDivisors G, if (Ideal.absNorm d:ℝ) ≤ Z then
        (UniqueFactorizationMonoid.moebius d:ℂ)*(c:ℂ) else 0) := by
  classical
  have hl : (∑ d ∈ idealDivisors G, if Z < (Ideal.absNorm d:ℝ) then
        (UniqueFactorizationMonoid.moebius d:ℂ)*(((c*X)/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0) =
      ((c*X:ℝ):ℂ)*(∑ d ∈ idealDivisors G, if Z < (Ideal.absNorm d:ℝ) then
        (UniqueFactorizationMonoid.moebius d:ℂ)/(Ideal.absNorm d:ℂ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : Z < (Ideal.absNorm d:ℝ)
    · simp only [hd,ite_true,Complex.ofReal_div,Complex.ofReal_natCast]
      ring
    · simp only [hd,ite_false,mul_zero]
  have hs : (∑ d ∈ idealDivisors G, if (Ideal.absNorm d:ℝ) ≤ Z then
        (UniqueFactorizationMonoid.moebius d:ℂ)*(c:ℂ) else 0) =
      (c:ℂ)*(∑ d ∈ idealDivisors G, if (Ideal.absNorm d:ℝ) ≤ Z then
        (UniqueFactorizationMonoid.moebius d:ℂ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : (Ideal.absNorm d:ℝ) ≤ Z <;> simp only [hd,ite_true,ite_false,mul_zero] ; ring
  rw [principalTruncation_eq_ideal_divisors G hG,hl,hs]
  unfold primePoolDensity
  push_cast
  ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem unrestrictedDualPrincipalTruncation_eq
    (W : ℝ → ℂ) (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Z : m → ℝ) (hM : 0 < M) (hF : 0 < F)
    (hrows : ∀ i, rows i ≠ 0) (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k)) :
    unrestrictedDualPrincipalTruncation W rows left right a b M F Z =
      paperRadialFourier W 0*unrestrictedPrincipalDensity rows left right a b (M/F) -
      paperRadialFourier W 0*unrestrictedLargePrincipalSum rows left right a b M F Z -
      W 0*unrestrictedSmallPrincipalSum rows left right a b M F (fun d i => (Ideal.absNorm d:ℝ) ≤ Z i) := by
  classical
  have hpos (I : Ideal O) (hI : I ≠ 0) : 0 < (Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))
  have ht (i : m) (j : n) (k : p) :
      unrestrictedPairTerm rows left right a b i j k *
        (((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ) *
          principalTruncation (fun P : primePool {left j*right k} => P.val) Finset.univ W
            (Real.sqrt (F*(Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ)/
              (M*(Ideal.absNorm (rows i):ℝ)))) (Z i)) =
      paperRadialFourier W 0 * (unrestrictedPairTerm rows left right a b i j k *
        ((Real.sqrt ((M/F)/(Ideal.absNorm (rows i):ℝ)):ℝ):ℂ)*primePoolDensity (left j*right k)) -
      paperRadialFourier W 0 * (unrestrictedPairTerm rows left right a b i j k *
        ∑ d ∈ idealDivisors (left j*right k), if Z i < (Ideal.absNorm d:ℝ) then
          (UniqueFactorizationMonoid.moebius d:ℂ)*
            ((Real.sqrt ((M/F)/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0) -
      W 0 * (unrestrictedPairTerm rows left right a b i j k *
        ∑ d ∈ idealDivisors (left j*right k), if (Ideal.absNorm d:ℝ) ≤ Z i then
          (UniqueFactorizationMonoid.moebius d:ℂ)*
            ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ) else 0) := by
    by_cases hc : IsCoprime (left j) (right k)
    · have hsq : Squarefree (left j*right k) :=
        squarefree_mul_iff.mpr ⟨hc.isRelPrime,(hleft j).2.1,(hright k).2.1⟩
      rw [principalTruncation_scaled _ hsq,dual_principal_prefactor_identity M F (Ideal.absNorm (rows i))
        (Ideal.absNorm (left j)) (Ideal.absNorm (right k)) hM hF
        (hpos _ (hrows i)) (hpos _ (hleft j).1) (hpos _ (hright k).1)]
      ring
    · have hz : unrestrictedPairTerm rows left right a b i j k = 0 := by
        simp only [unrestrictedPairTerm,hc,ite_false]
      simp only [hz,zero_mul,mul_zero,sub_zero]
  unfold unrestrictedDualPrincipalTruncation
  simp_rw [ht]
  simp only [unrestrictedPrincipalDensity,unrestrictedLargePrincipalSum,unrestrictedSmallPrincipalSum,
    Finset.sum_sub_distrib,Finset.mul_sum]

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson UnrestrictedIdealReindex GaussGeneratorTransport

theorem dualPrincipalIdeal_truncated_all_conductors
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (V : 𝓢(ℝ,ℂ)) (X Y Z lengthScale : ℝ) (hX : 0<X) :
    dualPrincipalIdeal I J V X = (6:ℂ)⁻¹ *
      (principalTruncation (fun P : primePool {I*J} => P.val) Finset.univ V X Z +
       middleTruncation (fun P : primePool {I*J} => P.val) Finset.univ V X Y Z lengthScale +
       truncationError (fun P : primePool {I*J} => P.val) Finset.univ V X Y Z lengthScale) := by
  let P := fun P : primePool {I*J} => P.val
  let f : O → ℂ := fun z => rowCoprimeMask P Finset.univ z *
    (if z=0 then 0 else V (‖eisEmbedding z‖^2/X))
  have hV : Summable (fun z : O => ‖V (‖eisEmbedding z‖^2/X)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest V X hX)
  have hf : Summable f := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hV
    intro z
    dsimp only [f]
    by_cases hz : z=0
    · simp only [hz,ite_true,mul_zero,norm_zero]
      exact norm_nonneg _
    · rw [if_neg hz,norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (QuadraticUnitInvariance.rowCoprimeMask_norm_le_one P Finset.univ z)
  have h0 : f 0=0 := by simp only [f,ite_true,mul_zero]
  have hu (u : Oˣ) (z : O) : f (u.val*z)=f z := by
    dsimp only [f]
    rw [QuadraticUnitInvariance.rowCoprimeMask_unit_mul,norm_eisEmbedding_unit_mul]
    simp only [mul_eq_zero,u.ne_zero,false_or]
  have he := tsum_unit_invariant_of_zero f hf h0 hu
  have hm (z : O) : rowCoprimeMask P Finset.univ z=idealZeroMask I z*idealZeroMask J z := by
    rw [singleton_rowCoprimeMask_eq_idealZeroMask,idealZeroMask_mul I J hI.1 hJ.1]
  have hd : (∑' A : NonzeroIdeal, f (idealGenerator A.val))=dualPrincipalIdeal I J V X := by
    unfold dualPrincipalIdeal
    apply tsum_congr
    intro A
    simp only [f,hm,if_neg (idealGenerator_ne_zero A.val A.property),idealGenerator_norm_sq]
  rw [hd] at he
  have hs : principalTruncation P Finset.univ V X Z + middleTruncation P Finset.univ V X Y Z lengthScale +
      truncationError P Finset.univ V X Y Z lengthScale = ∑' z : O, f z := by
    unfold truncationError
    dsimp only [f]
    ring
  change dualPrincipalIdeal I J V X=(6:ℂ)⁻¹ *
    (principalTruncation P Finset.univ V X Z + middleTruncation P Finset.univ V X Y Z lengthScale +
      truncationError P Finset.univ V X Y Z lengthScale)
  rw [hs,he]
  ring

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

theorem unrestrictedDualPrincipal_error_uniform (l : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n],
      ∀ (ε : ℝ) (hε : 0 < ε) (B N M F T : ℝ),
        1 ≤ B → 1 ≤ N → 0 < M → 0 < F → 4 ≤ T →
        ∀ (rows : m → Ideal O) (cols : n → Ideal O),
          Function.Injective rows → Function.Injective cols →
          (∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B) →
          (∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) →
          ∀ (a : n → ℂ) (W : 𝓢(ℝ, ℂ)),
          ‖unrestrictedDualPrincipalErrorSum rows cols a W M F N T‖ ≤
            16384 * B * N *
              ((2 * M / (F * N)) * ((supportConstant ε hε * (N * N) ^ ε) *
                (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ l)) *
              ∑ j, ‖a j‖ ^ 2 := by
  obtain ⟨s, C, hC, hb⟩ := primePool_symmetric_error_bound l
  refine ⟨s, C, hC, ?_⟩
  intro m n _ _ _ _ ε hε B N M F T hB hN hM hF hT rows cols hr hc hrows hcols a W
  let E₀ := (supportConstant ε hε * (N * N) ^ ε) *
    (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ l
  let error : m → n → n → ℂ := fun i j k =>
    (((M / (Real.sqrt ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) * F) : ℝ) : ℂ) *
      truncationError (fun P : primePool {cols j * cols k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))))
        ((N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))) / T)
        (T * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) (T ^ 4))
  have hsc := (supportConstant_pos ε hε).le
  have hE₀ : 0 ≤ E₀ := by dsimp only [E₀]; positivity
  have herr (i : m) (j k : n) : ‖error i j k‖ ≤ (2 * M / (F * N)) * E₀ := by
    have hi : 0 < (Ideal.absNorm (rows i) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h => (hrows i).1 (Ideal.absNorm_eq_zero_iff.mp h))
    obtain ⟨hX₀, hlo, hhi⟩ := dual_truncation_reference_bounds M F (Ideal.absNorm (rows i)) N
      (Ideal.absNorm (cols j)) (Ideal.absNorm (cols k)) hM hF hi (by linarith) (hcols j).2 (hcols k).2
    have hh := hb ε hε (cols j * cols k) (mul_ne_zero (hcols j).1.1 (hcols k).1.1) W
      _ _ T hX₀ hlo hhi hT
    simp only [map_mul, Nat.cast_mul] at hh
    have he : ‖truncationError (fun P : primePool {cols j * cols k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))))
        ((N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))) / T)
        (T * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) (T ^ 4)‖ ≤ E₀ := by
      apply hh.trans
      dsimp only [E₀]
      gcongr
      · exact (hcols j).2.2
      · exact (hcols k).2.2
    dsimp only [error]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul
      (dual_truncation_prefactor_bound M F N (Ideal.absNorm (cols j)) (Ideal.absNorm (cols k))
        hM hF (by linarith) (hcols j).2 (hcols k).2) he (norm_nonneg _) (by positivity)
  exact unrestricted_pair_error_ideal_bound rows cols hr hc B N hB hN hrows
    (fun j => ⟨(hcols j).1.1, (hcols j).2.2⟩) a _ (by positivity) error herr

section
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
theorem retainedDualPrincipalSum_symmetric_truncation
    (W : 𝓢(ℝ,ℂ)) (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ)
    (M F N T : ℝ) (hM : 0<M) (hF : 0<F)
    (hrows : ∀ i, rows i ≠ 0) (hcols : ∀ j, Admissible (cols j)) :
    (6:ℂ)*retainedDualPrincipalSum W rows cols a M F =
      unrestrictedDualPrincipalTruncation W rows cols cols a a M F
        (fun i => T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))) +
      unrestrictedDualTruncatedMiddle W rows cols cols a a M F
        (fun i => (N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))/T)
        (fun i => T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))) (T^4) +
      unrestrictedDualPrincipalErrorSum rows cols a W M F N T := by
  have hpos (I : Ideal O) (hI : I ≠ 0) : 0 < (Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))
  unfold retainedDualPrincipalSum unrestrictedDualPrincipalTruncation
    unrestrictedDualTruncatedMiddle unrestrictedDualPrincipalErrorSum
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [dualPrincipalIdeal_truncated_all_conductors (cols j) (cols k) (hcols j) (hcols k)]
  · ring
  · have hi := hpos _ (hrows i)
    have hj := hpos _ (hcols j).1
    have hk := hpos _ (hcols k).1
    exact Real.sqrt_pos.mpr (by positivity : 0 <
      F*(Ideal.absNorm (cols j):ℝ)*(Ideal.absNorm (cols k):ℝ)/(M*(Ideal.absNorm (rows i):ℝ)))

end

lemma norm_four_correction_terms (A B C D : ℂ) :
    ‖-A-B+C+D‖ ≤ ‖A‖+‖B‖+‖C‖+‖D‖ := by
  have hab := norm_sub_le (-A) B
  have habc := norm_add_le (-A-B) C
  have habcd := norm_add_le (-A-B+C) D
  simp only [norm_neg] at hab
  linarith

theorem retained_dual_principal_difference (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        {α : ℝ} (hexp : HasSieveExponent α), 1/2 ≤ α →
      ∀ (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) (B N M F T : ℝ),
        1≤B → 1≤N → 0<M → 0<F → 4≤T →
      ∀ (rows : m → Ideal O) (cols : n → Ideal O),
        Function.Injective rows → Function.Injective cols →
        (∀ i, Squarefree (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B) →
        (∀ j, Admissible (cols j) ∧ N/2 ≤ (Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ) ≤ N) →
        (∀ j k, columnRay (cols j)=columnRay (cols k)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)),
        ‖(6:ℂ)*retainedDualPrincipalSum W rows cols a M F -
          paperRadialFourier W 0*unrestrictedPrincipalDensity rows cols cols a a (M/F)‖ ≤
        ‖paperRadialFourier W 0‖*(4*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a a) +
        ‖W 0‖*(4*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F T a a) +
        4*dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F T a a W +
        16384*B*N*((2*M/(F*N))*((supportConstant ε hε*(N*N)^ε)*
          (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/T^l))*∑ j, ‖a j‖^2 := by
  obtain ⟨s,C,hC,herr⟩ := unrestrictedDualPrincipal_error_uniform l
  refine ⟨s,C,hC,?_⟩
  intro m n _ _ _ _ α hexp hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT rows cols hr hc hrows hcols hray a W
  let Z := fun i => T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))
  let Y := fun i => (N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))/T
  have hT0 : 0≤T := by linarith
  have hmain := unrestrictedDualPrincipalTruncation_eq W rows cols cols a a M F Z hM hF
    (fun i => (hrows i).1.ne_zero) (fun j => (hcols j).1) (fun k => (hcols k).1)
  have hsplit := retainedDualPrincipalSum_symmetric_truncation W rows cols a M F N T hM hF
    (fun i => (hrows i).1.ne_zero) (fun j => (hcols j).1)
  change (6:ℂ)*retainedDualPrincipalSum W rows cols a M F =
    unrestrictedDualPrincipalTruncation W rows cols cols a a M F Z +
    unrestrictedDualTruncatedMiddle W rows cols cols a a M F Y Z (T^4) +
    unrestrictedDualPrincipalErrorSum rows cols a W M F N T at hsplit
  have heq : (6:ℂ)*retainedDualPrincipalSum W rows cols a M F -
      paperRadialFourier W 0*unrestrictedPrincipalDensity rows cols cols a a (M/F) =
      -(paperRadialFourier W 0*unrestrictedLargePrincipalSum rows cols cols a a M F Z) -
      (W 0*unrestrictedSmallPrincipalSum rows cols cols a a M F (fun d i => (Ideal.absNorm d:ℝ)≤Z i)) +
      unrestrictedDualTruncatedMiddle W rows cols cols a a M F Y Z (T^4) +
      unrestrictedDualPrincipalErrorSum rows cols a W M F N T := by
    rw [hsplit,hmain]
    ring
  have hl := hexp.unrestricted_large_principal_sum hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT
    rows cols cols hr hc hc hrows (fun j => ⟨(hcols j).1,(hcols j).2.2⟩)
    (fun k => ⟨(hcols k).1,(hcols k).2.2⟩) hray a a Z (fun _ => le_rfl)
  have hs := hexp.unrestricted_small_principal_sum hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT0
    rows cols cols hr hc hc hrows hcols hcols hray a a (fun d i => (Ideal.absNorm d:ℝ)≤Z i)
    (fun _ _ h => h)
  have hm := hexp.unrestricted_dual_truncated_middle hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT0
    rows cols cols hr hc hc hrows a a W Y Z (T^4) hcols hcols hray (fun _ => le_rfl)
  have he := herr ε hε B N M F T hB hN hM hF hT rows cols hr hc
    (fun i => ⟨(hrows i).1.ne_zero,(hrows i).2.2⟩) hcols a W
  rw [heq]
  apply (norm_four_correction_terms _ _ _ _).trans
  rw [norm_mul,norm_mul]
  exact add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hl (norm_nonneg _))
    (mul_le_mul_of_nonneg_left hs (norm_nonneg _))) hm) he

lemma sum_ideal_subtype_dyadic {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal O)) (K : ℝ) (f : Ideal O → A) :
    (∑ I : S, f I.val) = ∑ j : Fin (columnDyadicLength K+1),
      ∑ I : divisorDyadicBin S K j, f I.val := by
  classical
  rw [Finset.sum_coe_sort S f,sum_divisorDyadicBins S K f]
  exact Finset.sum_congr rfl (fun j _ => (Finset.sum_coe_sort (divisorDyadicBin S K j) f).symm)

lemma retainedDualMajorant_nonneg {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0≤C) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (B N M F T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ))
    (hB : 0≤B) (hN : 0≤N) (hM : 0≤M) (hF : 0≤F) (hT : 0≤T) :
    0≤ retainedDualMajorant s C l hexp deltaLoss hδ ε hε B N M F T a W := by
  have hs0 := smallPrincipalMajorant_nonneg hexp deltaLoss hδ ε hε B N M F (1/2) a a hB hN hM hF (by norm_num)
  have hs1 := smallPrincipalMajorant_nonneg hexp deltaLoss hδ ε hε B N M F T a a hB hN hM hF hT
  have hm := dualMiddleMajorant_nonneg hexp deltaLoss hδ ε hε B N M F T a a W hB hN hM hF hT
  have hc := (supportConstant_pos ε hε).le
  unfold retainedDualMajorant
  positivity

lemma retainedDualMajorant_mono {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0≤C) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (B' B N M F T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ))
    (hB' : 0≤B') (hB : B'≤B) (hN : 0≤N) (hM : 0≤M) (hF : 0≤F) (hT : 0≤T) :
    retainedDualMajorant s C l hexp deltaLoss hδ ε hε B' N M F T a W ≤
      retainedDualMajorant s C l hexp deltaLoss hδ ε hε B N M F T a W := by
  have hB0 := hB'.trans hB
  have hα0 : 0≤α-1/2 := by linarith
  have he := divisorEnergyFactor_nonneg ε hε N a a
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  have hs := (supportConstant_pos ε hε).le
  have hlat := nonzeroLatticeEnvelopeConstant_nonneg
  have hW := dualMiddleDecayConstant_nonneg W
  unfold retainedDualMajorant smallPrincipalMajorant dualMiddleMajorant
  gcongr

lemma retainedDualPrincipalDifference_dyadic {n : Type} [Fintype n] [DecidableEq n]
    (W : 𝓢(ℝ,ℂ)) (S : Finset (Ideal O)) (K : ℝ) (cols : n → Ideal O) (a : n → ℂ) (M F : ℝ) :
    (6:ℂ)*retainedDualPrincipalSum W (fun I : S => I.val) cols a M F -
      paperRadialFourier W 0*unrestrictedPrincipalDensity (fun I : S => I.val) cols cols a a (M/F) =
    ∑ j : Fin (columnDyadicLength K+1),
      ((6:ℂ)*retainedDualPrincipalSum W (fun I : divisorDyadicBin S K j => I.val) cols a M F -
        paperRadialFourier W 0*unrestrictedPrincipalDensity
          (fun I : divisorDyadicBin S K j => I.val) cols cols a a (M/F)) := by
  classical
  have h := sum_ideal_subtype_dyadic (A := ℂ) S K (fun I =>
    (6:ℂ)*retainedDualPrincipalSum W (fun _ : Unit => I) cols a M F -
      paperRadialFourier W 0*unrestrictedPrincipalDensity (fun _ : Unit => I) cols cols a a (M/F))
  simpa only [retainedDualPrincipalSum,unrestrictedPrincipalDensity,unrestrictedPairTerm,
    Finset.mul_sum,←Finset.sum_sub_distrib,Fintype.sum_unique] using h

theorem retained_dual_principal_global (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] {α : ℝ} (hexp : HasSieveExponent α), 1/2≤α →
      ∀ (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) (K N M F T : ℝ),
        1≤K → 1≤N → 0<M → 0<F → 4≤T →
      ∀ (cols : n → Ideal O), Function.Injective cols →
        (∀ j, Admissible (cols j) ∧ N/2≤(Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
        (∀ j k, columnRay (cols j)=columnRay (cols k)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)),
        ‖(6:ℂ)*retainedDualPrincipalSum W (fun I : squarefreeIdealRange K => I.val) cols a M F -
          paperRadialFourier W 0*unrestrictedPrincipalDensity
            (fun I : squarefreeIdealRange K => I.val) cols cols a a (M/F)‖ ≤
        (columnDyadicLength K+1:ℕ)*retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M F T a W := by
  obtain ⟨s,C,hC,hbound⟩ := retained_dual_principal_difference l
  refine ⟨s,C,hC,?_⟩
  intro n _ _ α hexp hα deltaLoss hδ ε hε K N M F T hK hN hM hF hT cols hc hcols hray a W
  classical
  let S := squarefreeIdealRange K
  let R := retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M F T a W
  have hS (I : Ideal O) (hI : I∈S) : 1≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K := by
    have hi := mem_squarefreeIdealRange.mp hI
    refine ⟨?_,hi.2⟩
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hi.1.ne_zero (Ideal.absNorm_eq_zero_iff.mp h))
  have hR : 0≤R := retainedDualMajorant_nonneg s C hC.le l hexp deltaLoss hδ ε hε (2*K) N M F T a W
    (by linarith) (by linarith) hM.le hF.le (by linarith)
  have hb (j : Fin (columnDyadicLength K+1)) :
      ‖(6:ℂ)*retainedDualPrincipalSum W (fun I : divisorDyadicBin S K j => I.val) cols a M F -
        paperRadialFourier W 0*unrestrictedPrincipalDensity
          (fun I : divisorDyadicBin S K j => I.val) cols cols a a (M/F)‖ ≤ R := by
    by_cases hj : (divisorDyadicBin S K j).Nonempty
    · let B := 2*divisorDyadicScale j.val
      have hB : 1≤B := by dsimp only [B]; linarith [divisorDyadicScale_ge_one j.val]
      have hBK : B≤2*K := by
        dsimp only [B]
        exact mul_le_mul_of_nonneg_left (divisorDyadicBin_scale_le S K hS j hj) (by norm_num)
      have hrows (I : divisorDyadicBin S K j) : Squarefree I.val ∧
          B/2≤(Ideal.absNorm I.val:ℝ) ∧ (Ideal.absNorm I.val:ℝ)≤B := by
        have hi := divisorDyadicBin_bounds S K hS j I.val I.property
        refine ⟨(mem_squarefreeIdealRange.mp (Finset.mem_filter.mp I.property).1).1,?_,hi.2⟩
        dsimp only [B]
        linarith
      have hh := hbound hexp hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT
        (fun I : divisorDyadicBin S K j => I.val) cols Subtype.val_injective hc hrows hcols hray a W
      apply hh.trans
      exact retainedDualMajorant_mono s C hC.le l hexp hα deltaLoss hδ ε hε B (2*K) N M F T a W
        (by linarith) hBK (by linarith) hM.le hF.le (by linarith)
    · have he := Finset.not_nonempty_iff_eq_empty.mp hj
      have : IsEmpty (divisorDyadicBin S K j) := by
        refine ⟨fun I => ?_⟩
        have hi := I.property
        simp only [he,Finset.notMem_empty] at hi
      simpa only [retainedDualPrincipalSum,unrestrictedPrincipalDensity,Finset.univ_eq_empty,
        Finset.sum_empty,mul_zero,sub_zero,norm_zero] using hR
  rw [retainedDualPrincipalDifference_dyadic W (squarefreeIdealRange K) K cols a M F]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : Fin (columnDyadicLength K+1), R := Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,R]

end

open scoped BigOperators Classical
open ActualEisensteinCubic QuadraticSquarefreeKernel CompletedGauss

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.PoissonComparison
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace CanonicalQuadraticSieve

section

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator

theorem divisorTwist_norm_le {n : Type} (cols : n → Ideal O) (a : n → ℂ)
    (q : Ideal O) (j : n) : ‖divisorTwist cols a q j‖≤‖a j‖ := by
  rw [divisorTwist,norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)

theorem retainedDualMajorant_coefficient_scale_le {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0≤C) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (B N M F T : ℝ) (a a' : n → ℂ) (W : 𝓢(ℝ,ℂ))
    (hB : 0≤B) (hN : 0<N) (hM : 0≤M) (hF : 1≤F) (hT : 0≤T)
    (ha : ∀j, ‖a' j‖≤‖a j‖) :
    retainedDualMajorant s C l hexp deltaLoss hδ ε hε B N M F T a' W ≤
      retainedDualMajorant s C l hexp deltaLoss hδ ε hε B N M 1 T a W := by
  have he := divisorEnergyFactor_mono_coefficients ε hε N a a' a a' ha ha
  have he0 := divisorEnergyFactor_nonneg ε hε N a' a'
  have he1 := divisorEnergyFactor_nonneg ε hε N a a
  have hea : (∑j, ‖a' j‖^2)≤∑j, ‖a j‖^2 :=
    Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (ha j) 2)
  have hs := (supportConstant_pos ε hε).le
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  have hlat := nonzeroLatticeEnvelopeConstant_nonneg
  have hW := dualMiddleDecayConstant_nonneg W
  have hF0 : 0<F := by linarith
  have hMF : M/F≤M := div_le_self hM hF
  have hNF : N≤F*N := by nlinarith
  have hMN : 2*M/(F*N)≤2*M/N :=
    div_le_div_of_nonneg_left (by positivity) hN hNF
  unfold retainedDualMajorant smallPrincipalMajorant dualMiddleMajorant
  simp only [div_one,one_mul]
  gcongr

theorem centeredRetainedDual_sum_bound_oai (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] {α : ℝ} (hexp : HasSieveExponent α), 1/2≤α →
      ∀ (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) (G : Ideal O), G≠0 →
      ∀ (K N M T : ℝ), 1≤K → 1≤N → 0<M → 4≤T →
      ∀ (cols : n → Ideal O), Function.Injective cols →
        (∀j, Admissible (cols j) ∧ N/2≤(Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
        (∀j k, columnRay (cols j)=columnRay (cols k)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)),
        (∑q∈idealDivisors G, ‖centeredRetainedDual W cols a M K q‖) ≤
          (idealDivisors G).card*(columnDyadicLength K+1:ℕ)*
            retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) := by
  obtain ⟨s,C,hC,hbound⟩ := retained_dual_principal_global l
  refine ⟨s,C,hC,?_⟩
  intro n _ _ α hexp hα deltaLoss hδ ε hε G hG K N M T hK hN hM hT cols hc hcols hray a W
  classical
  have hqbound (q : Ideal O) (hq : q∈idealDivisors G) :
      ‖centeredRetainedDual W cols a M K q‖ ≤
        (columnDyadicLength K+1:ℕ)*
          retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) := by
    have hqd := (mem_idealDivisors hG).mp hq
    have hq0 : q≠0 := by intro hz; rw [hz,zero_dvd_iff] at hqd; exact hG hqd
    have hq1 : 1≤(Ideal.absNorm q:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hq0 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hh := hbound hexp hα deltaLoss hδ ε hε K N M (Ideal.absNorm q:ℝ) T hK hN hM
      (by linarith) hT cols hc hcols hray (divisorTwist cols a q) (quadraticTransformedSquareProfile W)
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact retainedDualMajorant_coefficient_scale_le s C hC.le l hexp deltaLoss hδ ε hε
      (2*K) N M (Ideal.absNorm q:ℝ) T a (divisorTwist cols a q) (quadraticTransformedSquareProfile W)
      (by linarith) (by linarith) hM.le hq1 (by linarith) (divisorTwist_norm_le cols a q)
  calc
    _ ≤ ∑_q∈idealDivisors G, (columnDyadicLength K+1:ℕ)*
        retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) :=
      Finset.sum_le_sum hqbound
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

end

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator

end

open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy

end CanonicalQuadraticSieve

open scoped BigOperators Classical

end

end OAI
end

theorem solution : type_of% @OAI.CanonicalQuadraticSieve.centeredRetainedDual_sum_bound_oai := @OAI.CanonicalQuadraticSieve.centeredRetainedDual_sum_bound_oai
