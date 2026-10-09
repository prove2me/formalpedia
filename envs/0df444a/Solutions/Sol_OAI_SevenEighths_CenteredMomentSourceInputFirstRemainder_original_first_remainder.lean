-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentSourceInputFirstRemainder.original_first_remainder
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:59:33.382766+00:00
-- url     : https://prove2.me/submissions/642b223e-0ed5-44fa-a44b-58d8f23c1c35

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_CenteredMomentSourceInputFirstSectorTail_local_input_tail

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

end ActualEisensteinCubic

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

theorem norm_finite_character_le_one {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (r : R) : ‖χ r‖ ≤ 1 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    simpa only [MulChar.coe_equivToUnitHom] using
      (Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)).le
  · rw [MulChar.map_nonunit χ hr, norm_zero]
    exact zero_le_one

theorem finiteSexticRow_norm_le_one {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (j : ι → ℕ) (a : O) :
    ‖finiteSexticRow P hg j a‖ ≤ 1 := by
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  rw [finiteSexticRow, norm_prod]
  calc
    _ ≤ ∏ i : ι, (1 : ℝ) := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun i _ => norm_finite_character_le_one
        (canonicalSextic (P i) (hg i) ^ j i) _)
    _ = 1 := by simp

end QuadraticInitialBound

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.DyadicColumns
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

theorem columnDyadicLength_small_power (ε : ℝ) (hε : 0 < ε) (N : ℝ) (hN : 1 ≤ N) :
    (columnDyadicLength N + 1 : ℝ) ≤ (2 + 1 / (ε * Real.log 2)) * N ^ ε := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 ≤ Real.log N / Real.log 2 := div_nonneg (Real.log_nonneg hN) hlog.le
  have hceil := Nat.ceil_lt_add_one hq
  have hL : (columnDyadicLength N + 1 : ℝ) ≤ 2 + Real.log N / Real.log 2 := by
    dsimp only [columnDyadicLength]
    linarith
  have hr : 1 ≤ N ^ ε := Real.one_le_rpow hN hε.le
  have hb : Real.log N / Real.log 2 ≤ (N ^ ε / ε) / Real.log 2 :=
    div_le_div_of_nonneg_right (Real.log_le_rpow_div (by linarith) hε) hlog.le
  calc
    _ ≤ 2 + Real.log N / Real.log 2 := hL
    _ ≤ 2 * N ^ ε + (N ^ ε / ε) / Real.log 2 := add_le_add (by linarith) hb
    _ = _ := by field_simp

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex QuadraticSquarefreeKernel

end CanonicalQuadraticSieve

open scoped BigOperators Classical

open scoped BigOperators Classical

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

open ActualEisensteinCubic

lemma divisorDyadicLabel_bounds (N : ℝ) (D : Ideal O)
    (hD : 1 ≤ (Ideal.absNorm D : ℝ)) (hDN : (Ideal.absNorm D : ℝ) ≤ N) :
    (2 : ℝ)^(divisorDyadicLabel N D).val/2 < (Ideal.absNorm D : ℝ) ∧
      (Ideal.absNorm D : ℝ) ≤ (2 : ℝ)^(divisorDyadicLabel N D).val := by
  unfold divisorDyadicLabel
  rw [dif_pos ⟨hD,hDN⟩]
  exact (positive_ideal_dyadic_exists N D hD hDN).choose_spec.2

theorem sum_divisorDyadicBins {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal O)) (N : ℝ) (f : Ideal O → A) :
    (∑ D ∈ S, f D) = ∑ j : Fin (columnDyadicLength N+1), ∑ D ∈ divisorDyadicBin S N j, f D := by
  simp only [divisorDyadicBin,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  simp

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.MeanSquare.TransformedColumns
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic

theorem finite_inverse_norm_sum (S : Finset (Ideal O)) (H : ℝ)
    (hS : ∀ I∈S,I≠0) (hH : ∀I∈S,(Ideal.absNorm I:ℝ)≤H) :
    (∑I∈S,1/(Ideal.absNorm I:ℝ))≤256*(columnDyadicLength H+1:ℝ) := by
  have hpos (I : Ideal O) (hI : I∈S) : 1≤(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hbin (j : Fin (columnDyadicLength H+1)) :
      (∑I∈divisorDyadicBin S H j,1/(Ideal.absNorm I:ℝ))≤256 := by
    have hp : 0<(2:ℝ)^j.val := by positivity
    have hone : 1≤(2:ℝ)^j.val := one_le_pow₀ (by norm_num)
    have hcount : ((divisorDyadicBin S H j).card:ℝ)≤128*(2:ℝ)^j.val := by
      apply DescentFiberCost.finite_ideal_count_real _ _ hone
      · intro I hI
        exact hS I (Finset.mem_filter.mp hI).1
      · intro I hI
        obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
        have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).2
        simpa only [hj] using hb
    have hterm (I : Ideal O) (hI : I∈divisorDyadicBin S H j) :
        1/(Ideal.absNorm I:ℝ)≤2/(2:ℝ)^j.val := by
      obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
      have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).1
      rw [hj] at hb
      apply (div_le_div_iff₀ (by linarith [hpos I hIS]) hp).mpr
      linarith
    calc
      _ ≤ ∑_I∈divisorDyadicBin S H j,2/(2:ℝ)^j.val := Finset.sum_le_sum hterm
      _ = ((divisorDyadicBin S H j).card:ℝ)*(2/(2:ℝ)^j.val) := by simp
      _ ≤ (128*(2:ℝ)^j.val)*(2/(2:ℝ)^j.val) := by gcongr
      _ = _ := by field_simp; ring
  rw [sum_divisorDyadicBins S H]
  calc
    _ ≤ ∑j : Fin (columnDyadicLength H+1),(256:ℝ) := Finset.sum_le_sum (fun j _ => hbin j)
    _ = _ := by simp; ring

open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel

open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.ProductColumns
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
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum

theorem product_fiber_card (P : Finset (Ideal O×Ideal O)) (I : Ideal O) (hI : I≠0) :
    (P.filter (fun p => p.1*p.2=I)).card≤(idealDivisors I).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    apply (mem_idealDivisors hI).mpr
    rw [←(Finset.mem_filter.mp hp).2]
    exact dvd_mul_right _ _
  · intro p hp q hq he
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    have hz : p.1≠0 := by intro hz; simp only [hz,zero_mul] at hp'; exact hI hp'.symm
    apply Prod.ext he
    apply mul_left_cancel₀ hz
    rw [hp',he,hq']

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.CubeBlocks
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
namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticSquarefreeKernel UniqueFactorizationMonoid

theorem powerfulBase_spec (I : Ideal O) (hI : PowerfulIdeal I) :
    powerfulBase I≠0 ∧ powerfulBase I ^2*squarefreePart I ^3=I := by
  rw [powerfulBase,dif_pos hI]
  exact (powerful_exists_square_cube I hI).choose_spec

theorem powerfulBase_injective_on_fiber (I J : Ideal O)
    (hI : PowerfulIdeal I) (hJ : PowerfulIdeal J)
    (hb : squarefreePart I=squarefreePart J) (ha : powerfulBase I=powerfulBase J) : I=J := by
  rw [←(powerfulBase_spec I hI).2,←(powerfulBase_spec J hJ).2,ha,hb]

theorem powerfulBase_norm_bound (I : Ideal O) (hI : PowerfulIdeal I) (X : ℝ)
    (hX : (Ideal.absNorm I:ℝ)≤X) :
    1≤(Ideal.absNorm (squarefreePart I):ℝ) ∧
    (Ideal.absNorm (squarefreePart I):ℝ)≤X ∧
    (Ideal.absNorm (powerfulBase I):ℝ)≤Real.sqrt X/(Ideal.absNorm (squarefreePart I):ℝ) := by
  have ha := (powerfulBase_spec I hI).1
  have hb := (squarefree_squarefreePart I).ne_zero
  have ha1 : 1≤(Ideal.absNorm (powerfulBase I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => ha (Ideal.absNorm_eq_zero_iff.mp hz))
  have hb1 : 1≤(Ideal.absNorm (squarefreePart I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hb (Ideal.absNorm_eq_zero_iff.mp hz))
  have hnorm : (Ideal.absNorm (powerfulBase I):ℝ)^2*(Ideal.absNorm (squarefreePart I):ℝ)^3=(Ideal.absNorm I:ℝ) := by
    have h := congrArg (fun J : Ideal O => (Ideal.absNorm J:ℝ)) (powerfulBase_spec I hI).2
    simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using h
  have hX0 : 0≤X := (Nat.cast_nonneg _).trans hX
  have hb2 : (Ideal.absNorm (squarefreePart I):ℝ)≤(Ideal.absNorm (squarefreePart I):ℝ)^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hb1 (show (1:ℕ)≤3 by decide)
  have hab : ((Ideal.absNorm (powerfulBase I):ℝ)*(Ideal.absNorm (squarefreePart I):ℝ))^2≤X := by
    calc
      _ = (Ideal.absNorm (powerfulBase I):ℝ)^2*(Ideal.absNorm (squarefreePart I):ℝ)^2 := by ring
      _ ≤ (Ideal.absNorm (powerfulBase I):ℝ)^2*(Ideal.absNorm (squarefreePart I):ℝ)^3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb1 (by decide)) (sq_nonneg _)
      _ ≤ X := hnorm.trans_le hX
  have hbX : (Ideal.absNorm (squarefreePart I):ℝ)≤X := by
    calc
      _ ≤ (Ideal.absNorm (squarefreePart I):ℝ)^3 := hb2
      _ ≤ (Ideal.absNorm (powerfulBase I):ℝ)^2*(Ideal.absNorm (squarefreePart I):ℝ)^3 :=
        le_mul_of_one_le_left (by positivity) (one_le_pow₀ ha1)
      _ ≤ X := hnorm.trans_le hX
  refine ⟨hb1,hbX,?_⟩
  apply (le_div_iff₀ (by linarith : 0<(Ideal.absNorm (squarefreePart I):ℝ))).mpr
  nlinarith [Real.sq_sqrt hX0,Real.sqrt_nonneg X]

end

open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticSquarefreeKernel

theorem powerful_fiber_count (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,PowerfulIdeal I ∧ (Ideal.absNorm I:ℝ)≤X)
    (B : Ideal O) (hB : B∈S.image squarefreePart) :
    ((S.filter (fun I => squarefreePart I=B)).card:ℝ)≤128*Real.sqrt X/(Ideal.absNorm B:ℝ) := by
  obtain ⟨I,hI,hIB⟩ := Finset.mem_image.mp hB
  have hi := hS I hI
  have hnorm := powerfulBase_norm_bound I hi.1 X hi.2
  rw [hIB] at hnorm
  have hAb : 1≤(Ideal.absNorm (powerfulBase I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => (powerfulBase_spec I hi.1).1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hscale : 1≤Real.sqrt X/(Ideal.absNorm B:ℝ) := hAb.trans hnorm.2.2
  let T := S.filter (fun I => squarefreePart I=B)
  have hinj : Set.InjOn powerfulBase T := by
    intro J hJ lengthScale hL he
    exact powerfulBase_injective_on_fiber J lengthScale (hS J (Finset.mem_filter.mp hJ).1).1
      (hS lengthScale (Finset.mem_filter.mp hL).1).1
      ((Finset.mem_filter.mp hJ).2.trans (Finset.mem_filter.mp hL).2.symm) he
  have hcard : (T.image powerfulBase).card=T.card := Finset.card_image_iff.mpr hinj
  have hcount := DescentFiberCost.finite_ideal_count_real (T.image powerfulBase)
    (Real.sqrt X/(Ideal.absNorm B:ℝ)) hscale (fun J hJ => by
      obtain ⟨lengthScale,hL,rfl⟩ := Finset.mem_image.mp hJ
      exact (powerfulBase_spec lengthScale (hS lengthScale (Finset.mem_filter.mp hL).1).1).1) (fun J hJ => by
      obtain ⟨lengthScale,hL,rfl⟩ := Finset.mem_image.mp hJ
      have hp := powerfulBase_norm_bound lengthScale (hS lengthScale (Finset.mem_filter.mp hL).1).1 X
        (hS lengthScale (Finset.mem_filter.mp hL).1).2
      simpa only [(Finset.mem_filter.mp hL).2] using hp.2.2)
  rw [hcard] at hcount
  simpa only [mul_div_assoc] using hcount

theorem powerful_ideal_count_log (S : Finset (Ideal O)) (X : ℝ) (hX : 1≤X)
    (hS : ∀I∈S,PowerfulIdeal I ∧ (Ideal.absNorm I:ℝ)≤X) :
    (S.card:ℝ)≤32768*Real.sqrt X*(columnDyadicLength X+1:ℝ) := by
  let B := S.image squarefreePart
  have hBn (J : Ideal O) (hJ : J∈B) : J≠0 ∧ (Ideal.absNorm J:ℝ)≤X := by
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ
    exact ⟨(squarefree_squarefreePart I).ne_zero,(powerfulBase_norm_bound I (hS I hI).1 X (hS I hI).2).2.1⟩
  have he : (S.card:ℝ)=∑J∈B,((S.filter (fun I => squarefreePart I=J)).card:ℝ) := by
    calc
      _ = ∑_I∈S,(1:ℝ) := by simp
      _ = ∑J∈B,∑_I∈S.filter (fun I => squarefreePart I=J),(1:ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun I hI => Finset.mem_image_of_mem squarefreePart hI) _).symm
      _ = _ := by simp
  rw [he]
  calc
    _ ≤ ∑J∈B,128*Real.sqrt X/(Ideal.absNorm J:ℝ) := Finset.sum_le_sum (fun J hJ => powerful_fiber_count S X hS J hJ)
    _ = (128*Real.sqrt X)*∑J∈B,1/(Ideal.absNorm J:ℝ) := by rw [Finset.mul_sum]; congr 1; ext J; ring
    _ ≤ (128*Real.sqrt X)*(256*(columnDyadicLength X+1:ℝ)) :=
      mul_le_mul_of_nonneg_left (finite_inverse_norm_sum B X (fun J hJ => (hBn J hJ).1)
        (fun J hJ => (hBn J hJ).2)) (by positivity)
    _ = _ := by ring

theorem powerful_ideal_count (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ (S : Finset (Ideal O)) (X : ℝ), 1≤X →
      (∀I∈S,PowerfulIdeal I ∧ (Ideal.absNorm I:ℝ)≤X) →
      (S.card:ℝ)≤C*X^(1/2+ε) := by
  let C := 32768*(2+1/(ε*Real.log 2))
  have hC : 0<C := by have hl : 0<Real.log 2 := Real.log_pos (by norm_num); dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro S X hX hS
  apply (powerful_ideal_count_log S X hX hS).trans
  calc
    _ ≤ 32768*Real.sqrt X*((2+1/(ε*Real.log 2))*X^ε) :=
      mul_le_mul_of_nonneg_left (columnDyadicLength_small_power ε hε X hX) (by positivity)
    _ = C*X^(1/2+ε) := by
      rw [Real.rpow_add (by linarith : 0<X),←Real.sqrt_eq_rpow]
      dsimp [C]
      ring

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Canonical
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentCanonical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCorrelation

theorem actualSextic_order_six (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (actualSextic P hg) = 6 := by
  let Φ : MulChar (O ⧸ P) O →* MulChar (O ⧸ P) ℂ :=
    MulChar.ringHomCompHom eisEmbedding
  have hΦ : Function.Injective Φ := by
    intro x y h
    apply MulChar.ext
    intro t
    apply eisEmbedding_injective
    exact congrArg (fun f : MulChar (O ⧸ P) ℂ => f t) h
  exact (orderOf_injective Φ hΦ _).trans (sexticChar_order P hg hchar)

end SevenEighths.CenteredMomentCanonical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CenteredExceptionalProfile
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredExceptionalProfile
open UniqueFactorizationMonoid HeckeFamily CanonicalRowCompletion
open ConcretePrimeRowBridge hiding O
open CompletedGauss hiding O
open ConcreteTraceCRT
local notation "O" => HeckeFamily.O
open CenteredExceptionalCount CenteredMomentCanonical
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem split_at_prime (I P : Ideal O) (hI : I ≠ 0) [P.IsMaximal] :
    ∃ J : Ideal O, I = P ^ valuation I P * J ∧ J ≠ 0 ∧ IsCoprime J P := by
  let S := (normalizedFactors I).toFinset
  let J := ∏ Q ∈ S.erase P, Q ^ valuation I Q
  have hsplit : I = P ^ valuation I P * J := by
    calc
      I = (normalizedFactors I).prod := (Ideal.prod_normalizedFactors_eq_self hI).symm
      _ = ∏ Q ∈ S, Q ^ valuation I Q := Finset.prod_multiset_count _
      _ = P ^ valuation I P * J := by
        by_cases hP : P ∈ S
        · exact (Finset.mul_prod_erase S (fun Q => Q ^ valuation I Q) hP).symm
        · have hz : valuation I P = 0 := Multiset.count_eq_zero.mpr
            (fun h => hP (Multiset.mem_toFinset.mpr h))
          simp only [J, Finset.erase_eq_of_notMem hP, hz, pow_zero, one_mul]
  refine ⟨J, hsplit, ?_, ?_⟩
  · intro hz
    apply hI
    rw [hsplit, hz, mul_zero]
  · apply IsCoprime.prod_left
    intro Q hQ
    obtain ⟨hQP, hQS⟩ := Finset.mem_erase.mp hQ
    have hp := prime_of_normalized_factor Q (Multiset.mem_toFinset.mp hQS)
    let : Q.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    exact (Ideal.isCoprime_of_isMaximal hQP).pow_left

theorem exists_unit_probe (Q K P : Ideal O) (hK : K ≠ 0) [P.IsMaximal]
    (hQP : IsCoprime Q P) (u : (O ⧸ P)ˣ) :
    ∃ n : O, n - 1 ∈ Q ∧ IsCoprime (Ideal.span {n}) K ∧
      Ideal.Quotient.mk P n = (u : O ⧸ P) := by
  obtain ⟨J, hsplit, hJ, hJP⟩ := split_at_prime K P hK
  let e := Ideal.quotientInfEquivQuotientProd (Q * J) P (hQP.mul_left hJP)
  obtain ⟨x, hx⟩ := e.surjective ((1 : O ⧸ Q * J), (u : O ⧸ P))
  obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (Ideal.Quotient.mk (Q * J) n, Ideal.Quotient.mk P n) = (1, (u : O ⧸ P)) at hx
  have hnQJ := congrArg Prod.fst hx
  have hnP := congrArg Prod.snd hx
  dsimp only at hnQJ hnP
  have hn : n - 1 ∈ Q * J := Ideal.Quotient.eq.mp (by simpa using hnQJ)
  have hnJ : Ideal.Quotient.mk J n = 1 :=
    (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (Ideal.mul_le_right hn)
  have hcJ : IsCoprime (Ideal.span {n}) J :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hnJ ▸ isUnit_one)
  have hcP : IsCoprime (Ideal.span {n}) P :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hnP ▸ u.isUnit)
  refine ⟨n, Ideal.mul_le_left hn, ?_, hnP⟩
  rw [hsplit]
  exact hcP.pow_right.mul_right hcJ

theorem valuation_mod_six_of_unit_agreement (Q K I J P : Ideal O)
    (hK : K ≠ 0) (hI : CanonicalQuadraticSieve.Supported I)
    (hJ : CanonicalQuadraticSieve.Supported J) [P.IsMaximal]
    (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (hQP : IsCoprime Q P)
    (heq : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      idealRowHom n I = idealRowHom n J) :
    valuation I P % 6 = valuation J P % 6 := by
  obtain ⟨I₀, hsplitI, hI₀, hcI⟩ := split_at_prime I P hI.1
  obtain ⟨J₀, hsplitJ, hJ₀, hcJ⟩ := split_at_prime J P hJ.1
  have hsI : CanonicalQuadraticSieve.Supported I₀ :=
    ((CanonicalQuadraticSieve.supported_mul_iff _ _).mp (hsplitI ▸ hI)).2
  have hsJ : CanonicalQuadraticSieve.Supported J₀ :=
    ((CanonicalQuadraticSieve.supported_mul_iff _ _).mp (hsplitJ ▸ hJ)).2
  have hpows : actualSextic P hg ^ valuation I P = actualSextic P hg ^ valuation J P := by
    apply MulChar.ext
    intro u
    obtain ⟨n, hn, hcK, hnP⟩ := exists_unit_probe (Q * I₀ * J₀) K P hK
      ((hQP.mul_left hcI).mul_left hcJ) u
    have hval := heq n (Ideal.mul_le_left (Ideal.mul_le_left hn)) hcK
    have hIn : n - 1 ∈ I₀ := Ideal.mul_le_right (Ideal.mul_le_left hn)
    have hJn : n - 1 ∈ J₀ := Ideal.mul_le_right hn
    rw [hsplitI, hsplitJ, map_mul, map_mul, map_pow, map_pow,
      idealRowHom_congr_mod I₀ n 1 hIn, idealRowHom_congr_mod J₀ n 1 hJn,
      idealRowHom_one_supported I₀ hsI, idealRowHom_one_supported J₀ hsJ,
      mul_one, mul_one, idealRowHom_prime n P hg, hnP] at hval
    simpa only [MulChar.pow_apply_coe] using hval
  have hm := (pow_eq_pow_iff_modEq.mp hpows)
  rw [actualSextic_order_six P hg hchar] at hm
  exact hm

end SevenEighths.CenteredExceptionalProfile

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Support
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentSupport
open UniqueFactorizationMonoid IdealMobiusDivisorSum CanonicalQuadraticSieve

theorem support_reconstruct (I : Ideal O) (hI : I ≠ 0) (S : Finset (Ideal O)) :
    supportExtract I S * supportResidual I S = I := by
  rw [supportExtract, supportResidual, ← Multiset.prod_add, Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self hI

open CompletedGauss hiding primeSupport
open CanonicalRowCompletion CenteredMomentSupportedCorrelation

end SevenEighths.CenteredMomentSupport
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Active
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentActive
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
open CanonicalRowCompletion CenteredMomentCanonical

theorem local_pair_reduction (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (c d : ℕ) (x : O ⧸ P) :
    (actualSextic P hg ^ c) x * star ((actualSextic P hg ^ d) x) =
      (actualSextic P hg ^ netExponent c d) x := by
  have h6 : actualSextic P hg ^ 6 = 1 := by
    rw [← actualSextic_order_six P hg hchar]
    exact pow_orderOf_eq_one _
  have h5 : actualSextic P hg ^ 5 = (actualSextic P hg)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ] using h6
  rw [MulChar.star_apply', ← MulChar.mul_apply]
  congr 1
  unfold netExponent
  rw [← actualSextic_order_six P hg hchar, pow_mod_orderOf,
    pow_add, pow_mul, h5, inv_pow]

theorem principal_product_eq_mask {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (B : Finset ι) (z : O) :
    (∏ i ∈ B, (1 : MulChar (O ⧸ P i) ℂ) (Ideal.Quotient.mk (P i) z)) =
      rowCoprimeMask P B z := by
  by_cases h : ∃ i ∈ B, z ∈ P i
  · rw [rowCoprimeMask, if_pos h]
    obtain ⟨i, hi, hz⟩ := h
    apply Finset.prod_eq_zero hi
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, MulChar.map_zero]
  · rw [rowCoprimeMask, if_neg h]
    apply Finset.prod_eq_one
    intro i hi
    apply MulChar.one_apply
    let : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
    apply isUnit_iff_ne_zero.mpr
    exact fun hz => h ⟨i, hi, Ideal.Quotient.eq_zero_iff_mem.mp hz⟩

variable {ι : Type*}

theorem common_ideal_pair_active (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ)
    (hc : ∀ i ∈ B, c i ≠ 0) (hd : ∀ i ∈ B, d i ≠ 0) (z : O) :
    idealRowHom z (∏ i ∈ B, P i ^ c i) *
      star (idealRowHom z (∏ i ∈ B, P i ^ d i)) =
      rowCoprimeMask P (principalSupport B c d) z *
        finiteSexticRow (fun i : activeSupport B c d => P i.val)
          (fun i => hg i.val) (fun i => netExponent (c i.val) (d i.val)) z := by
  let f := fun i => (actualSextic (P i) (hg i) ^ netExponent (c i) (d i))
    (Ideal.Quotient.mk (P i) z)
  have hlocal : idealRowHom z (∏ i ∈ B, P i ^ c i) *
      star (idealRowHom z (∏ i ∈ B, P i ^ d i)) = ∏ i ∈ B, f i := by
    simp only [map_prod, map_pow, star_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [idealRowHom_prime z (P i) (hg i),
      ← MulChar.pow_apply' _ (hc i hi), ← MulChar.pow_apply' _ (hd i hi)]
    exact local_pair_reduction (P i) (hg i) (hchar i) (c i) (d i) _
  have hzero : (∏ i ∈ B.filter (fun i => netExponent (c i) (d i) = 0), f i) =
      rowCoprimeMask P (principalSupport B c d) z := by
    rw [← principal_product_eq_mask]
    apply Finset.prod_congr rfl
    intro i hi
    have he := (Finset.mem_filter.mp hi).2
    simp only [f, he, pow_zero]
  rw [hlocal, ← Finset.prod_filter_mul_prod_filter_not B
    (fun i => netExponent (c i) (d i) = 0) f, hzero]
  congr 1
  exact (Finset.prod_coe_sort (s := activeSupport B c d) (f := f)).symm

open ConcreteTraceCRT EisensteinSchwartzPoisson

end SevenEighths.CenteredMomentActive
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Twist
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentTwist
open ActualEisensteinCubic EisensteinSchwartzPoisson
open CenteredMomentLattice

lemma norm_real_imaginary_power (X t : ℝ) (hX : 0 < X) :
    ‖(X : ℂ) ^ (Complex.I * t)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
  simp

end SevenEighths.CenteredMomentTwist
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RowNorm
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentRowNorm
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentCorrelation CenteredMomentFourier CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport
local notation "O" => ActualEisensteinCubic.O

theorem row_pair_summable (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O =>
      (idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b}))) *
        W (‖eisEmbedding z‖ ^ 2 / K)) := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  have h := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
    (Ideal.Quotient.mk (Ideal.span {a * b})) (pairResidue a b ha hb)
  simpa only [pairResidue_mk, scaledRadialTest_apply] using h

theorem rowPolynomial_norm_sq {α : Type*} (S : Finset α) (a : α → O)
    (c : α → ℂ) (z : O) :
    ((‖rowPolynomial S a c z‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (idealRowHom z (Ideal.span {a i}) * star (idealRowHom z (Ideal.span {a j}))) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [rowPolynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem rowEnergy_expand {α : Type*} (S : Finset α) (a : α → O) (c : α → ℂ)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    rowEnergy S a c W K =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        ∑' z : O, (idealRowHom z (Ideal.span {a i}) *
          star (idealRowHom z (Ideal.span {a j}))) * W (‖eisEmbedding z‖ ^ 2 / K) := by
  have hs (i j : α) := (row_pair_summable (a i) (a j) (ha i) (ha j) W K hK).mul_left
    (c i * star (c j))
  simp only [mul_assoc] at hs
  simp only [rowEnergy, rowPolynomial_norm_sq, Finset.sum_mul, mul_assoc]
  rw [Summable.tsum_finsetSum (fun i _ => (hasSum_sum (fun j _ => (hs i j).hasSum)).summable)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Summable.tsum_finsetSum (fun j _ => hs i j)]
  simp only [tsum_mul_left]

end SevenEighths.CenteredMomentRowNorm

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ZeroMode
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentZeroMode
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open ConcreteTraceCRT CubicEisenstein
open CenteredMomentRowNorm CenteredMomentCorrelation CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentFourier
open UniqueFactorizationMonoid CenteredExceptionalCount CenteredExceptionalProfile
local notation "O" => ActualEisensteinCubic.O

theorem pairResidue_unit_eq_one_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) (u : (Residue (a * b))ˣ) :
    pairResidue a b ha hb u = 1 := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  rw [pairFourier_zero, tsum_fintype] at hm
  have he : pairResidue a b ha hb u * (∑ x : Residue (a * b), pairResidue a b ha hb x) =
      ∑ x : Residue (a * b), pairResidue a b ha hb x := by
    simpa only [Finset.mul_sum, pairResidue_mul] using
      u.mulLeft_bijective.sum_comp (pairResidue a b ha hb)
  exact (mul_right_cancel₀ hm (he.trans (one_mul _).symm))

theorem rows_agree_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) (n : O)
    (hn : IsCoprime (Ideal.span {n}) (Ideal.span {a} * Ideal.span {b})) :
    idealRowHom n (Ideal.span {a}) = idealRowHom n (Ideal.span {b}) := by
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {a * b}) n) := by
    apply (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr
    simpa only [Ideal.span_singleton_mul_span_singleton] using hn
  have he := pairResidue_unit_eq_one_of_mean_ne_zero a b ha hb hm hunit.unit
  rw [hunit.unit_spec, pairResidue_mk] at he
  let := finite_quotient_span (supported_element_ne_zero b hb)
  have hu : IsUnit (Ideal.Quotient.mk (Ideal.span {b}) n) :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hn.of_mul_right_right
  have hj : idealRowHom n (Ideal.span {b}) * star (idealRowHom n (Ideal.span {b})) = 1 := by
    change supportedModulusCharacter b hb (Ideal.Quotient.mk _ n) *
      star (supportedModulusCharacter b hb (Ideal.Quotient.mk _ n)) = 1
    rw [MulChar.star_apply', ← MulChar.mul_apply, mul_inv_cancel]
    exact MulChar.one_apply hu
  exact mul_right_cancel₀ (by intro hz; simp [hz] at hj) (he.trans hj.symm)

theorem valuation_profile_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) (P : Ideal O) [P.IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ P)
    (hodd : ringChar (O ⧸ P) ≠ 2) :
    valuation (Ideal.span {a}) P % 6 = valuation (Ideal.span {b}) P % 6 := by
  apply valuation_mod_six_of_unit_agreement 1
    (Ideal.span {a} * Ideal.span {b}) _ _ P (mul_ne_zero ha.1 hb.1) ha hb
    hg hodd isCoprime_one_left
  intro n _ hn
  exact rows_agree_of_mean_ne_zero a b ha hb hm n hn

theorem powerful_product_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) :
    CompletedGauss.PowerfulIdeal (Ideal.span {a} * Ideal.span {b}) := by
  have hs := (supported_mul_iff _ _).mpr ⟨ha, hb⟩
  refine ⟨hs.1, ?_⟩
  intro P hP
  obtain ⟨hmax, hg, hodd⟩ := supported_factors_good _ hs P hP
  let := hmax
  have he := valuation_profile_of_mean_ne_zero a b ha hb hm P hg hodd
  have hp := Multiset.count_pos.mpr hP
  rw [normalizedFactors_mul ha.1 hb.1, Multiset.count_add] at hp ⊢
  unfold valuation at he
  omega

theorem powerful_pair_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O × Ideal O)) (Y : ℝ), 1 ≤ Y →
      (∀ p ∈ S, CompletedGauss.PowerfulIdeal (p.1 * p.2) ∧
        (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ Y) →
      (S.card : ℝ) ≤ C * Y ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hp⟩ := CompletedGauss.powerful_ideal_count (ε / 2) (by positivity)
  obtain ⟨D, hD, hd⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) (by positivity)
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro S Y hY hS
  let T := S.image (fun p : Ideal O × Ideal O => p.1 * p.2)
  have hT (I : Ideal O) (hI : I ∈ T) :
      CompletedGauss.PowerfulIdeal I ∧ (Ideal.absNorm I : ℝ) ≤ Y := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI
    exact hS p hp
  have hcard : (S.card : ℝ) = ∑ I ∈ T,
      ((S.filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I)).card : ℝ) := by
    calc
      _ = ∑ _p ∈ S, (1 : ℝ) := by simp
      _ = ∑ I ∈ T, ∑ _p ∈ S.filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I), (1 : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun p hp =>
          Finset.mem_image_of_mem (fun p : Ideal O × Ideal O => p.1 * p.2) hp) _).symm
      _ = _ := by simp
  rw [hcard]
  calc
    _ ≤ ∑ I ∈ T, D * Y ^ (ε / 2) := by
      apply Finset.sum_le_sum
      intro I hI
      calc
        _ ≤ ((IdealMobiusDivisorSum.idealDivisors I).card : ℝ) := by
          exact_mod_cast product_fiber_card S I (hT I hI).1.1
        _ ≤ D * (Ideal.absNorm I : ℝ) ^ (ε / 2) := hd I (hT I hI).1.1
        _ ≤ D * Y ^ (ε / 2) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) (hT I hI).2 (by positivity)) hD.le
    _ = (T.card : ℝ) * (D * Y ^ (ε / 2)) := by simp
    _ ≤ (C * Y ^ (1 / 2 + ε / 2)) * (D * Y ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_right (hp T Y hY hT) (by positivity)
    _ = (C * D) * (Y ^ (1 / 2 + ε / 2) * Y ^ (ε / 2)) := by ring
    _ = (C * D) * Y ^ (1 / 2 + ε) := by
      rw [← Real.rpow_add (by linarith : 0 < Y)]
      congr 2
      ring

theorem pairFourier_zero_norm_le (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) :
    ‖pairFourier a b ha hb 0‖ ≤ (Ideal.absNorm (Ideal.span {a * b}) : ℝ) := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  rw [pairFourier_zero, tsum_fintype]
  calc
    _ ≤ ∑ x : Residue (a * b), ‖pairResidue a b ha hb x‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue (a * b), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [pairResidue_mk, norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (idealRowHom_norm _ _)).trans
        (idealRowHom_norm _ _)
    _ = _ := by simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem scaled_zero_mean_norm_le (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (K : ℝ) (hK : 0 ≤ K) :
    ‖((K / ‖eisEmbedding (a * b)‖ ^ 2 : ℝ) : ℂ) * pairFourier a b ha hb 0‖ ≤ K := by
  have hn : (0 : ℝ) < Ideal.absNorm (Ideal.span {a * b}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero
        (supported_element_ne_zero a ha) (supported_element_ne_zero b hb))))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    eisEmbedding_norm_sq_eq_absNorm_span, abs_of_nonneg (div_nonneg hK hn.le)]
  calc
    _ ≤ (K / (Ideal.absNorm (Ideal.span {a * b}) : ℝ)) *
        (Ideal.absNorm (Ideal.span {a * b}) : ℝ) :=
      mul_le_mul_of_nonneg_left (pairFourier_zero_norm_le a b ha hb) (div_nonneg hK hn.le)
    _ = K := div_mul_cancel₀ _ hn.ne'

theorem nonzero_mean_pair_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α β : Type*} (S : Finset (α × β))
      (a : α → O) (b : β → O)
      (ha : ∀ i, Supported (Ideal.span {a i}))
      (hb : ∀ j, Supported (Ideal.span {b j})) (Y : ℝ), 1 ≤ Y →
      Set.InjOn (fun p : α × β => (Ideal.span {a p.1}, Ideal.span {b p.2})) S →
      (∀ p ∈ S, (Ideal.absNorm (Ideal.span {a p.1} * Ideal.span {b p.2}) : ℝ) ≤ Y) →
      ((S.filter (fun p : α × β => pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 ≠ 0)).card : ℝ)
        ≤ C * Y ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hc⟩ := powerful_pair_count ε hε
  refine ⟨C, hC, ?_⟩
  intro α β S a b ha hb Y hY hinj hN
  let T := S.filter (fun p : α × β => pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 ≠ 0)
  let f := fun p : α × β => (Ideal.span {a p.1}, Ideal.span {b p.2})
  have hf : Set.InjOn f (T : Set (α × β)) := by
    intro p hp q hq he
    exact hinj (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 he
  have ht : (T.image f).card = T.card := Finset.card_image_of_injOn hf
  have hbound := hc (T.image f) Y hY (by
    intro I hI
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI
    have hp' := Finset.mem_filter.mp hp
    exact ⟨powerful_product_of_mean_ne_zero (a p.1) (b p.2) (ha p.1) (hb p.2) hp'.2,
      hN p hp'.1⟩)
  simpa only [ht] using hbound

theorem first_zero_sum_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α β : Type*} (S : Finset (α × β))
      (a : α → O) (b : β → O)
      (ha : ∀ i, Supported (Ideal.span {a i}))
      (hb : ∀ j, Supported (Ideal.span {b j})) (d : α × β → ℂ)
      (Y K B : ℝ), 1 ≤ Y → 0 ≤ K → 0 ≤ B →
      Set.InjOn (fun p : α × β => (Ideal.span {a p.1}, Ideal.span {b p.2})) S →
      (∀ p ∈ S, (Ideal.absNorm (Ideal.span {a p.1} * Ideal.span {b p.2}) : ℝ) ≤ Y) →
      (∀ p ∈ S, ‖d p‖ ≤ B) →
      ‖∑ p ∈ S, d p * (((K / ‖eisEmbedding (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
        pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0)‖ ≤
        C * K * B * Y ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hc⟩ := nonzero_mean_pair_count ε hε
  refine ⟨C, hC, ?_⟩
  intro α β S a b ha hb d Y K B hY hK hB hinj hN hd
  let T := S.filter (fun p : α × β => pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 ≠ 0)
  have hsum : (∑ p ∈ S, d p * (((K / ‖eisEmbedding (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
      pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0)) =
      ∑ p ∈ T, d p * (((K / ‖eisEmbedding (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
      pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hpt
    have hz : pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 = 0 := by
      simpa only [T, Finset.mem_filter, hp, true_and, not_not] using hpt
    rw [hz, mul_zero, mul_zero]
  rw [hsum]
  calc
    _ ≤ ∑ p ∈ T, ‖d p * (((K / ‖eisEmbedding (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
        pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ T, B * K := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      exact mul_le_mul (hd p (Finset.mem_filter.mp hp).1)
        (scaled_zero_mean_norm_le _ _ _ _ K hK) (norm_nonneg _) hB
    _ = (T.card : ℝ) * (B * K) := by simp
    _ ≤ (C * Y ^ (1 / 2 + ε)) * (B * K) :=
      mul_le_mul_of_nonneg_right (hc S a b ha hb Y hY hinj hN) (mul_nonneg hB hK)
    _ = C * K * B * Y ^ (1 / 2 + ε) := by ring

theorem ideal_zero_energy_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
      (c : Ideal O → ℂ) (X K B : ℝ), 1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ X) →
      (∀ I ∈ S, ‖c I‖ ≤ B) →
      ‖idealZeroEnergy S hS c K‖ ≤ C * K * B ^ 2 * X ^ (1 + ε) := by
  obtain ⟨C, hC, hc⟩ := first_zero_sum_bound (ε / 2) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro S hS c X K B hX hK hB hN hd
  have hinj : Set.InjOn (fun p : S × S =>
      (Ideal.span {idealColumn S p.1}, Ideal.span {idealColumn S p.2}))
        (↑(Finset.univ : Finset (S × S)) : Set (S × S)) := by
    intro p _ q _ he
    apply Prod.ext
    · exact Subtype.ext (by simpa only [idealColumn_span] using congrArg Prod.fst he)
    · exact Subtype.ext (by simpa only [idealColumn_span] using congrArg Prod.snd he)
  have hNpair (p : S × S) (_hp : p ∈ (Finset.univ : Finset (S × S))) :
      (Ideal.absNorm (Ideal.span {idealColumn S p.1} * Ideal.span {idealColumn S p.2}) : ℝ) ≤ X ^ 2 := by
    rw [idealColumn_span, idealColumn_span, map_mul, Nat.cast_mul, pow_two]
    exact mul_le_mul (hN _ p.1.property) (hN _ p.2.property) (Nat.cast_nonneg _) (by linarith)
  have hdPair (p : S × S) (_hp : p ∈ (Finset.univ : Finset (S × S))) :
      ‖c p.1.val * star (c p.2.val)‖ ≤ B ^ 2 := by
    rw [norm_mul, norm_star, pow_two]
    exact mul_le_mul (hd _ p.1.property) (hd _ p.2.property) (norm_nonneg _) hB
  have hh := hc Finset.univ (idealColumn S) (idealColumn S)
    (idealColumn_supported S hS) (idealColumn_supported S hS)
    (fun p : S × S => c p.1.val * star (c p.2.val)) (X ^ 2) K (B ^ 2)
    (by nlinarith) hK (sq_nonneg _) hinj hNpair hdPair
  have hp : (X ^ 2) ^ (1 / 2 + ε / 2 : ℝ) = X ^ (1 + ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ X)]
    congr 1
    ring
  simpa only [idealZeroEnergy, Fintype.sum_prod_type, hp] using hh

end SevenEighths.CenteredMomentZeroMode

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AddedZeroUniform
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAddedZeroUniform
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentGaussEnergy CenteredMomentAddedZero CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

lemma tupleEquiv_slot {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) (v : Tuple ι) (i : ι) :
    tupleEquiv e v ((e i).castAdd 2) = v (Sum.inl i) := by
  change v ((coordinateEquiv e).symm _) = _
  have h : coordinateEquiv e (Sum.inl i) = (e i).castAdd 2 := by
    simp only [coordinateEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inl, finSumFinEquiv_apply_left]
  rw [← h, Equiv.symm_apply_apply]

lemma tupleEquiv_plain {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) (v : Tuple ι) (j : Fin 2) :
    tupleEquiv e v (j.natAdd n) = v (Sum.inr j) := by
  change v ((coordinateEquiv e).symm _) = _
  have h : coordinateEquiv e (Sum.inr j) = j.natAdd n := by
    simp only [coordinateEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inr, finSumFinEquiv_apply_right, Equiv.refl_apply]
  rw [← h, Equiv.symm_apply_apply]

theorem tupleProduct_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (v : Tuple ι) :
    tupleProduct (tupleEquiv e v) = finiteTupleProduct v := by
  exact (coordinateEquiv e).symm.prod_comp v

theorem originalCoefficient_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O) (v : Tuple ι) :
    originalCoefficient n c χ R t (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j))
      (fun j => P (e.symm j)) W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (tupleEquiv e v) =
    originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v := by
  have hslot (j : Fin n) : tupleEquiv e v (j.castAdd 2) = v (Sum.inl (e.symm j)) := by
    simpa only [Equiv.apply_symm_apply] using tupleEquiv_slot e v (e.symm j)
  have hp₀ : (⟨n, by omega⟩ : Fin (n + 2)) = (0 : Fin 2).natAdd n := by ext; simp
  have hp₁ : (⟨n + 1, by omega⟩ : Fin (n + 2)) = (1 : Fin 2).natAdd n := by ext; simp
  simp only [originalCoefficient, originalFiniteCoefficient, tupleProduct_reindex,
    hslot, hp₀, hp₁, tupleEquiv_plain]
  rw [e.symm.prod_comp (fun j => ν j (v (Sum.inl j)) * Wslot j ((Ideal.absNorm (v (Sum.inl j)) : ℝ) / P j))]

end SevenEighths.CenteredMomentAddedZeroUniform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CompleteCommon
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCompleteCommon
open UniqueFactorizationMonoid IdealMobiusDivisorSum CenteredMomentSupport
open CenteredExceptionalCount CenteredMomentRankinRadical CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem reconstruct (I J : Ideal O) (hI : I ≠ 0) :
    I = commonPart I J * residualPart I J := by
  rw [commonPart_eq_supportExtract, residualPart_eq_supportResidual]
  exact (support_reconstruct I hI _).symm

end SevenEighths.CenteredMomentCompleteCommon

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstReduced
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstReduced
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier
open CenteredMomentActive
local notation "O" => ActualEisensteinCubic.O

theorem tripleRow_mul (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ)
    (hG : ∀ x y,G (x*y)=G x*G y) (x y : O) :
    tripleRow a b r χa χb G (x*y)=tripleRow a b r χa χb G x*tripleRow a b r χa χb G y := by
  simp only [tripleRow,map_mul,hG]
  ring

theorem tripleRow_radial_summable (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z : O => tripleRow a b r χa χb G z*W (‖eisEmbedding z‖^2/K)) := by
  let := finite_quotient_span (mul_ne_zero ha (mul_ne_zero hb hr))
  let : Fintype (Residue (a*(b*r))) := Fintype.ofFinite _
  have hh := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
    (Ideal.Quotient.mk (Ideal.span {a*(b*r)})) (tripleResidue a b r χa χb G)
  simpa only [tripleResidue_mk,scaledRadialTest_apply] using hh

theorem tripleRow_poisson (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑' z : O,tripleRow a b r χa χb G z*W (‖eisEmbedding z‖^2/K)) =
      ((K/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*∑' h : O,
        tripleFourier a b r ha hb hr χa χb G h*
          paperRadialFourier W (K*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*r))‖^2) := by
  let := finite_quotient_span (mul_ne_zero ha (mul_ne_zero hb hr))
  let : Fintype (Residue (a*(b*r))) := Fintype.ofFinite _
  have hh := actual_radial_paper_poisson_trace W K hK (a*(b*r))
    (mul_ne_zero ha (mul_ne_zero hb hr)) (tripleResidue a b r χa χb G)
  simpa only [tripleResidue_mk,tripleFourier,quotientTrace,tsum_fintype,Complex.real_smul] using hh

theorem masked_triple_poisson {α : Type*} (P : α → Ideal O)
    [∀ i,(P i).IsMaximal] (hinj : Function.Injective P) (S : Finset α)
    (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (hG : ∀ x y,G (x*y)=G x*G y)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑' z : O,rowCoprimeMask P S z*tripleRow a b r χa χb G z*W (‖eisEmbedding z‖^2/K)) =
      ∑ E ∈ S.powerset,
        let e := primeSubsetGenerator P E
        let k := K/‖eisEmbedding e‖^2
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E,P i):ℂ)*tripleRow a b r χa χb G e*
          (((k/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*∑' h : O,
            tripleFourier a b r ha hb hr χa χb G h*
              paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*r))‖^2)) := by
  rw [tsum_masked_radial_dilations P hinj S _ (tripleRow_mul a b r χa χb G hG) W K
    (tripleRow_radial_summable a b r ha hb hr χa χb G W K hK)]
  apply Finset.sum_congr rfl
  intro E hE
  rw [tripleRow_poisson a b r ha hb hr χa χb G W _ (primeSubset_reducedScale_pos P E hK)]

theorem principalSexticRow_mul {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (j : ι → ℕ) (r : O) (hr : Ideal.span {r}=∏ i,P i) (x y : Residue r) :
    principalSexticRow P hcop hg j r hr (x*y)=
      principalSexticRow P hcop hg j r hr x*principalSexticRow P hcop hg j r hr y := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul,principalSexticRow_mk P hcop hg j r hr (x*y),
    principalSexticRow_mk P hcop hg j r hr x,principalSexticRow_mk P hcop hg j r hr y,
    finiteSexticRow_mul P hg j x y]

theorem common_residual_reduced_poisson {ι : Type*}
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i) (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (B : Finset ι) (c d : ι → ℕ) (hc : ∀ i∈B,c i≠0) (hd : ∀ i∈B,d i≠0)
    (a b : O) (ha : a≠0) (hb : b≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    let Q := fun i : activeSupport B c d => P i.val
    let hj := fun i : activeSupport B c d => netExponent (c i.val) (d i.val)
    let r := finitePrimeModulus Q
    let G := principalSexticRow Q (activePrimes_pairwise_coprime P hinj B c d)
      (fun i => hg i.val) hj r (span_finitePrimeModulus Q)
    (∑' z : O,χa (Ideal.Quotient.mk _ z)*χb (Ideal.Quotient.mk _ z)*
      (CanonicalRowCompletion.idealRowHom z (∏ i∈B,P i^c i)*
        star (CanonicalRowCompletion.idealRowHom z (∏ i∈B,P i^d i)))*
      W (‖eisEmbedding z‖^2/K)) =
      ∑ E ∈ (principalSupport B c d).powerset,
        let e := primeSubsetGenerator P E
        let k := K/‖eisEmbedding e‖^2
        (UniqueFactorizationMonoid.moebius (∏ i∈E,P i):ℂ)*tripleRow a b r χa χb G e*
          (((k/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*∑' h : O,
            tripleFourier a b r ha hb (finitePrimeModulus_ne_zero Q) χa χb G h*
              paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*r))‖^2)) := by
  dsimp only
  rw [← masked_triple_poisson P hinj (principalSupport B c d) a b _ ha hb
    (finitePrimeModulus_ne_zero _) χa χb _
    (principalSexticRow_mul _ _ _ _ _ _) W K hK]
  apply tsum_congr
  intro z
  rw [common_ideal_pair_active P hg hchar B c d hc hd]
  simp only [tripleRow,principalSexticRow_mk (fun i : activeSupport B c d => P i.val)
    (activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
    (fun i => netExponent (c i.val) (d i.val)) _ (span_finitePrimeModulus _) z]
  ring

end SevenEighths.CenteredMomentFirstReduced

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CanonicalFirst
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentCanonicalFirst
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredExceptionalCount
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation
open CenteredMomentFirstReduced CenteredMomentActive
open CenteredMomentCompleteCommon UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

theorem common_odd (I J : Ideal O) (hI : Supported I) (P : CommonIndex I J) :
    ringChar (O ⧸ P.val)≠2 :=
  (supported_factors_good I hI P.val (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)).2.2

theorem rightExponent_pos (I J : Ideal O) (P : CommonIndex I J) : 0< rightExponent I J P :=
  (common_valuations_pos I J P.val P.property).2

theorem commonPart_right_product (I J : Ideal O) :
    commonPart J I=∏ P : CommonIndex I J,P.val^rightExponent I J P := by
  unfold commonPart
  rw [commonSupport_comm J I]
  exact (Finset.prod_coe_sort (s:=commonSupport I J) (f:=fun P => P^valuation J P)).symm

theorem original_pair_factor (I J : Ideal O) (hI : Supported I) (hJ : Supported J) (z : O) :
    idealRowHom z I*star (idealRowHom z J)=
      residualCharacter I J hI (Ideal.Quotient.mk _ z)*
        (residualCharacter J I hJ)⁻¹ (Ideal.Quotient.mk _ z)*
        (idealRowHom z (∏ P : CommonIndex I J,P.val^leftExponent I J P)*
          star (idealRowHom z (∏ P : CommonIndex I J,P.val^rightExponent I J P))) := by
  let := finite_quotient_span (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
  rw [← MulChar.star_apply',residualCharacter_mk,residualCharacter_mk,
    ← commonPart_left_product,← commonPart_right_product]
  have hi := congrArg (idealRowHom z) (reconstruct I J hI.1)
  have hj := congrArg (idealRowHom z) (reconstruct J I hJ.1)
  simp only [map_mul] at hi hj
  rw [hi,hj,star_mul]
  ring

theorem canonical_pair_reduced_poisson (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑' z : O,(idealRowHom z I*star (idealRowHom z J))*W (‖eisEmbedding z‖^2/K))=
      reducedFirstSum I J hI hJ W K := by
  simp_rw [original_pair_factor I J hI hJ]
  exact common_residual_reduced_poisson (fun P : CommonIndex I J => P.val) Subtype.val_injective
    (common_good I J hI) (common_odd I J hI) Finset.univ (leftExponent I J) (rightExponent I J)
    (fun P _ => ne_of_gt (leftExponent_pos I J P)) (fun P _ => ne_of_gt (rightExponent_pos I J P))
    (residualGenerator I J) (residualGenerator J I)
    (supported_element_ne_zero _ (residualGenerator_supported I J hI))
    (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
    (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ W K hK

end SevenEighths.CenteredMomentCanonicalFirst

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceRow
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentRowNorm HeckeFamily CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_split (η : Character) (m A z : O) (t : ℝ) (I : Ideal O) :
    rowWeight η m A z t I = rowWeight η m A 1 t I*idealRowHom z I := by
  change (idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t) =
    ((idealCoeff η I*idealRowHom (m^6*(A*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))*idealRowHom z I
  rw [mul_one,← mul_assoc,idealRowHom_argument_mul]
  ring

theorem rowWeight_zero_of_not_supported (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) (I : Ideal O) (hI : ¬Supported I) :
    rowWeight η m A z t I=0 := by
  by_cases h0 : I=0
  · rw [h0,map_zero]
  let n := idealGenerator I
  have hn : n ≠ 0 := idealGenerator_ne_zero I h0
  have hs : Ideal.span {n}=I := span_idealGenerator I
  have hz := rowTwist_zero_of_not_supported (HeckeRowClosure.elementHom η) m 1 (A*z) n
    hmLam hm2 (hs ▸ hI)
  have he : rowTwist (HeckeRowClosure.elementHom η) m 1 (A*z) n =
      idealCoeff η I*idealRowHom (m^6*(A*z)) I := by
    change elementCoeff η n*idealRowHom (m^6*1^4*(A*z)) (Ideal.span {n})=_
    rw [one_pow,mul_one,hs,← idealCoeff_span η hn,hs]
  rw [he] at hz
  change (idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)=0
  rw [hz,zero_mul]

theorem finite_hecke_sum_eq_rowPolynomial (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) :
    (∑ I∈S,c I*rowWeight η m A z t I) =
      rowPolynomial Finset.univ (sourceGenerator S)
        (fun I : supportedColumns S => c I*rowWeight η m A 1 t I) z := by
  have he : (∑ I∈S,c I*rowWeight η m A z t I) =
      ∑ I∈supportedColumns S,c I*rowWeight η m A z t I := by
    symm
    apply Finset.sum_filter_of_ne
    intro I hI hn
    by_contra hs
    exact hn (by rw [rowWeight_zero_of_not_supported η m A z t hmLam hm2 I hs,mul_zero])
  rw [he,← Finset.sum_coe_sort (supportedColumns S) (fun I => c I*rowWeight η m A z t I)]
  unfold rowPolynomial
  apply Finset.sum_congr rfl
  intro I hI
  rw [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2,rowWeight_split]
  ring

theorem finiteHeckeEnergy_eq (η : Character) (m A : O) (t : ℝ)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    finiteHeckeEnergy η m A t S c W K =
      rowEnergy Finset.univ (sourceGenerator S)
        (fun I : supportedColumns S => c I*rowWeight η m A 1 t I) W K := by
  unfold finiteHeckeEnergy rowEnergy
  simp_rw [finite_hecke_sum_eq_rowPolynomial η m A _ t hmLam hm2 S c]

end SevenEighths.CenteredMomentSourceRow

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstEnergy
open CenteredMomentCanonicalFirst CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentHeckeExpansion HeckeFamily ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

theorem finiteHeckeEnergy_reduced_poisson (η : Character) (m A : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    finiteHeckeEnergy η m A t S c W K =
      ∑ I : supportedColumns S,∑ J : supportedColumns S,
        ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
          reducedFirstSum I J (Finset.mem_filter.mp I.property).2
            (Finset.mem_filter.mp J.property).2 W K := by
  rw [finiteHeckeEnergy_eq η m A t hmLam hm2 S c W K,
    rowEnergy_expand Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S => c I*rowWeight η m A 1 t I)
      (sourceGenerator_supported S) W K hK]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [sourceGenerator,sourceGenerator,
    primary_span_supported I (Finset.mem_filter.mp I.property).2,
    primary_span_supported J (Finset.mem_filter.mp J.property).2,
    canonical_pair_reduced_poisson]
  exact hK

end SevenEighths.CenteredMomentFirstEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceMass
namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.CenteredMomentSourceMass
open CenteredMomentAddedZero CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

lemma profileProduct_mem_box {r : ℕ} (W : Fin r → ℝ → ℂ) (b q : Fin r → ℝ)
    (hq : ∀ i, 0<q i) (hzero : ∀ i, W i 0=0)
    (hs : ∀ i x, W i x ≠ 0 → x ≤ b i)
    (v : Fin r → Ideal O) (hv : profileProduct W q v ≠ 0) :
    v ∈ tupleBox (fun i => b i*q i) := by
  apply (mem_tupleBox _ _).mpr
  intro i
  have hw : W i ((Ideal.absNorm (v i):ℝ)/q i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hv) i (Finset.mem_univ i)
  refine ⟨?_,(div_le_iff₀ (hq i)).mp (hs i _ hw)⟩
  intro hz
  apply hw
  simp only [hz,map_zero,Nat.cast_zero,zero_div,hzero]

lemma sourceProfiles_product {N : ℕ} (Wslot : Fin N → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O) (v : Fin (N+2) → Ideal O) :
    profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v =
      (∏ j : Fin N, Wslot j ((Ideal.absNorm (v (j.castAdd 2)):ℝ)/P j)) *
      (W₁ ((Ideal.absNorm (B₁*v ⟨N,by omega⟩):ℝ)/X₁) *
       W₂ ((Ideal.absNorm (B₂*v ⟨N+1,by omega⟩):ℝ)/X₂)) := by
  simp only [profileProduct,Fin.prod_univ_add,sourceProfiles,sourceScales,
    Fin.append_left,Fin.append_right,Fin.prod_univ_two,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,map_mul,Nat.cast_mul,div_div_eq_mul_div]
  have h₀ : Fin.natAdd N (0:Fin 2)=⟨N,by omega⟩ := by ext; simp
  have h₁ : Fin.natAdd N (1:Fin 2)=⟨N+1,by omega⟩ := by ext; simp
  rw [h₀,h₁]
  congr 2 <;> congr 1 <;> ring

lemma sourceBounds_product {N : ℕ} (b : Fin N → ℝ) (b₁ b₂ : ℝ) :
    (∏ i, sourceBounds b b₁ b₂ i) = (∏ j,b j)*b₁*b₂ := by
  simp only [sourceBounds,Fin.prod_univ_add,Fin.append_left,Fin.append_right,
    Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring

lemma sourceScales_product {N : ℕ} (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O) :
    (∏ i, sourceScales P X₁ X₂ B₁ B₂ i) =
      (∏ j,P j)*(X₁*X₂)/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂) := by
  simp only [sourceScales,Fin.prod_univ_add,Fin.append_left,Fin.append_right,
    Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring

lemma sourceScales_pos {N : ℕ} (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hB₁ : B₁≠0) (hB₂ : B₂≠0) :
    ∀ i, 0<sourceScales P X₁ X₂ B₁ B₂ i := by
  have hn₁ : (0:ℝ)<Ideal.absNorm B₁ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hn₂ : (0:ℝ)<Ideal.absNorm B₂ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  simp only [Fin.forall_fin_add,sourceScales,Fin.append_left,Fin.append_right,Fin.forall_fin_two]
  exact ⟨hP,div_pos hX₁ hn₁,div_pos hX₂ hn₂⟩

theorem originalCoefficient_factor (N : ℕ) (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (ν : Fin N → Ideal O → ℂ)
    (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Fin (N+2) → Ideal O) :
    originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v =
      (∏ j,ν j (v (j.castAdd 2))) * idealWeight c χ R t (tupleProduct v) *
      (profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v -
       profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v) *
      (if s∣tupleProduct v then 1 else 0) := by
  rw [originalCoefficient,Finset.prod_mul_distrib,sourceProfiles_product,sourceProfiles_product]
  unfold idealRectangle
  ring

lemma sourcePool_nonzero {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (v : Fin (N+2) → Ideal O)
    (hv : v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) : tupleProduct v ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rcases Finset.mem_union.mp (Finset.mem_filter.mp hv).1 with h|h <;>
    exact ((mem_tupleBox _ _).mp h i).1

theorem originalCoefficient_mem_sourcePool (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P b : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0)
    (hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0)
    (hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤ sourceBounds b b₁ b₂ i)
    (v : Fin (N+2) → Ideal O)
    (hv : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v ≠ 0) :
    v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ := by
  rw [originalCoefficient_factor] at hv
  have hslots := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).1).1
  have hd := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).2
  apply Finset.mem_filter.mpr
  refine ⟨?_,fun j => (Finset.prod_ne_zero_iff.mp hslots) j (Finset.mem_univ j)⟩
  apply Finset.mem_union.mpr
  by_cases hx : profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v = 0
  · apply Or.inr
    have hy : profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v ≠ 0 := by
      intro hy; exact hd (by rw [hx,hy,sub_self])
    exact profileProduct_mem_box _ _ _ (sourceScales_pos _ _ _ _ _ hP hY₁ hY₂ hB₁ hB₂) hzero hs v hy
  · exact Or.inl (profileProduct_mem_box _ _ _ (sourceScales_pos _ _ _ _ _ hP hX₁ hX₂ hB₁ hB₂) hzero hs v hx)

lemma source_coordinate_product {N : ℕ} (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ T : ℝ) (B₁ B₂ : Ideal O) (hT : X₁*X₂=T) :
    (∏ i,sourceBounds b b₁ b₂ i*sourceScales P X₁ X₂ B₁ B₂ i) =
      sourceRadius b P b₁ b₂ T B₁ B₂ := by
  rw [Finset.prod_mul_distrib,sourceBounds_product,sourceScales_product,hT]
  unfold sourceRadius
  ring

lemma tupleBox_product_bound {r : ℕ} (H : Fin r → ℝ) (v : Fin r → Ideal O)
    (hv : v ∈ tupleBox H) : (Ideal.absNorm (tupleProduct v):ℝ) ≤ ∏ i,H i := by
  simp only [tupleProduct,map_prod,Nat.cast_prod]
  exact Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
    (fun i _ => ((mem_tupleBox H v).mp hv i).2)

theorem sourcePool_product_bound {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) (v : Fin (N+2) → Ideal O)
    (hv : v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) :
    (Ideal.absNorm (tupleProduct v):ℝ) ≤ sourceRadius b P b₁ b₂ T B₁ B₂ := by
  rcases Finset.mem_union.mp (Finset.mem_filter.mp hv).1 with hx|hy
  · exact (tupleBox_product_bound _ v hx).trans_eq (source_coordinate_product b P b₁ b₂ X₁ X₂ T B₁ B₂ hX)
  · exact (tupleBox_product_bound _ v hy).trans_eq (source_coordinate_product b P b₁ b₂ Y₁ Y₂ T B₁ B₂ hY)

theorem originalCoefficient_product_bound (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P b : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0)
    (hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤ sourceBounds b b₁ b₂ i)
    (v : Fin (N+2) → Ideal O)
    (hv : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    tupleProduct v≠0 ∧ (Ideal.absNorm (tupleProduct v):ℝ)≤ sourceRadius b P b₁ b₂ T B₁ B₂ := by
  have hm := originalCoefficient_mem_sourcePool N c χ R t ν Wslot P b W₁ W₂ b₁ b₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hzero hs v hv
  exact ⟨sourcePool_nonzero _ _ _ _ _ _ _ _ _ _ _ v hm,
    sourcePool_product_bound _ _ _ _ _ _ _ _ _ _ _ _ hX hY v hm⟩

open CenteredMomentAddedZeroUniform

end SevenEighths.CenteredMomentSourceMass

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceProfileMass
namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.CenteredMomentSourceProfileMass
open ActualEisensteinCubic CenteredMomentPrimary CenteredMomentRectangle
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
local notation "O" => ActualEisensteinCubic.O

 theorem primary_mod_one (χ : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) (I : Ideal O) :
    primaryIdealCharacter 1 χ I=1 := by
  rw [primaryIdealCharacter_apply]
  have he : Ideal.Quotient.mk (Ideal.span {(1:O)}) (CompletedGauss.primaryGenerator I)=1 := by
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {(1:O)}))]
    apply Ideal.Quotient.eq.mpr
    rw [Ideal.span_singleton_one]
    trivial
  rw [he,map_one]

 theorem idealWeight_mod_one (χ : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) (R I : Ideal O) :
    CenteredMomentRectangle.idealWeight 1 χ R 0 I=(if IsCoprime I R then 1 else 0) := by
  simp only [idealWeight,primary_mod_one,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one]

 theorem profileCoefficient_eq_original {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=
      originalFiniteCoefficient 1 (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0
        ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v := by
  rw [originalFiniteCoefficient,idealWeight_mod_one]
  rfl

end SevenEighths.CenteredMomentSourceProfileMass

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SectorLocalization
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSectorLocalization
open CubicEisenstein ConcreteTraceCRT EisensteinSchwartzPoisson CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

theorem cutoff_bounds (x : ℝ) : 0 ≤ cutoff x ∧ cutoff x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem cutoff_antitone : Antitone cutoff := by
  intro x y hxy
  exact Real.smoothTransition.monotone (by linarith)

theorem annulus_bounds (x : ℝ) : 0 ≤ annulus x ∧ annulus x ≤ 1 := by
  by_cases hx : x ≤ 1/4
  · rw [annulus_zero_low x hx]; constructor <;> norm_num
  have hm := cutoff_antitone (show x ≤ 2*x by linarith)
  have h₁ := cutoff_bounds x
  have h₂ := cutoff_bounds (2*x)
  unfold annulus
  constructor <;> linarith

theorem dyadicScale_add (n : ℤ) : dyadicScale (n+1)=2*dyadicScale n := by
  simp only [dyadicScale,zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),zpow_one]
  ring

theorem dyadicWeight_bounds (n : ℤ) (q : ℝ) :
    0 ≤ dyadicWeight n q ∧ dyadicWeight n q ≤ 1 := annulus_bounds _

theorem dyadicWeight_outside_pair (q : ℝ) (k : ℤ)
    (hlo : dyadicScale k ≤ q) (hhi : q < dyadicScale (k+1))
    (n : ℤ) (hn : n ∉ ({k+1,k+2} : Finset ℤ)) : dyadicWeight n q=0 := by
  have hn₁ : n ≠ k+1 := by simpa using fun h => hn (by simp [h])
  have hn₂ : n ≠ k+2 := by simpa using fun h => hn (by simp [h])
  by_cases hnk : n ≤ k
  · exact dyadicWeight_zero_high n q ((zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hnk).trans hlo)
  · have hkn : k+3 ≤ n := by omega
    have hmono : dyadicScale (k+3) ≤ dyadicScale n :=
      zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hkn
    have he : dyadicScale (k+3)=4*dyadicScale (k+1) := by
      rw [show k+3=(k+1)+1+1 by omega,dyadicScale_add,dyadicScale_add]
      ring
    apply dyadicWeight_zero_low
    rw [he] at hmono
    linarith

theorem dyadicWeight_finite (q : ℝ) : (Function.support (fun n => dyadicWeight n q)).Finite := by
  by_cases hq : 0 < q
  · obtain ⟨k,hlo,hhi⟩ := exists_mem_Ico_zpow hq (by norm_num : (1:ℝ) < 2)
    apply (Set.toFinite (({k+1,k+2} : Finset ℤ) : Set ℤ)).subset
    intro n hn
    by_contra hh
    exact hn (dyadicWeight_outside_pair q k hlo hhi n hh)
  · have hz : ∀ n,dyadicWeight n q=0 := fun n =>
      dyadicWeight_zero_low n q ((le_of_not_gt hq).trans (div_nonneg (dyadicScale_pos n).le (by norm_num)))
    simp [hz]

theorem dyadicWeight_summable (q : ℝ) : Summable (fun n => dyadicWeight n q) :=
  summable_of_hasFiniteSupport (dyadicWeight_finite q)

theorem dyadicWeight_partition (q : ℝ) (hq : 0 < q) : ∑' n,dyadicWeight n q=1 := by
  obtain ⟨k,hlo,hhi⟩ := exists_mem_Ico_zpow hq (by norm_num : (1:ℝ) < 2)
  rw [tsum_eq_sum (s := {k+1,k+2}) (dyadicWeight_outside_pair q k hlo hhi)]
  change dyadicScale k ≤ q at hlo
  change q < dyadicScale (k+1) at hhi
  have hk : k+1 ≠ k+2 := by omega
  rw [Finset.sum_pair hk]
  simp only [dyadicWeight,annulus]
  have h₁ : 2*(q/dyadicScale (k+1))=q/dyadicScale k := by
    rw [dyadicScale_add]; field_simp
  have h₂ : 2*(q/dyadicScale (k+2))=q/dyadicScale (k+1) := by
    rw [show k+2=(k+1)+1 by omega,dyadicScale_add]; field_simp
  rw [h₁,h₂,cutoff_zero _ ((le_div_iff₀ (dyadicScale_pos k)).mpr (by simpa using hlo))]
  have hs : q/dyadicScale (k+2) ≤ 1/2 := by
    apply (div_le_iff₀ (dyadicScale_pos (k+2))).mpr
    rw [show k+2=(k+1)+1 by omega,dyadicScale_add]
    linarith
  rw [cutoff_one _ hs]
  ring

theorem retained_summable (R q : ℝ) :
    Summable (fun n : ℤ => if Retained R n then dyadicWeight n q else 0) :=
  (dyadicWeight_summable q).indicator {n | Retained R n}

theorem discarded_summable (R q : ℝ) :
    Summable (fun n : ℤ => if Retained R n then 0 else dyadicWeight n q) := by
  have h := (dyadicWeight_summable q).sub (retained_summable R q)
  convert (preTransparency := .instances) h using 1
  ext n
  split_ifs <;> simp

theorem retained_add_discarded (R q : ℝ) (hq : 0 < q) :
    retainedWeight R q+discardedWeight R q=1 := by
  rw [retainedWeight,discardedWeight,← (retained_summable R q).tsum_add (discarded_summable R q)]
  convert (preTransparency := .instances) dyadicWeight_partition q hq using 1
  apply tsum_congr
  intro n
  split_ifs <;> simp

theorem dyadicWeight_zero_nonpos (n : ℤ) (q : ℝ) (hq : q ≤ 0) : dyadicWeight n q=0 :=
  dyadicWeight_zero_low n q (hq.trans (div_nonneg (dyadicScale_pos n).le (by norm_num)))

theorem retainedWeight_zero_nonpos (R q : ℝ) (hq : q ≤ 0) : retainedWeight R q=0 := by
  simp [retainedWeight,dyadicWeight_zero_nonpos _ q hq]

theorem discardedWeight_zero_nonpos (R q : ℝ) (hq : q ≤ 0) : discardedWeight R q=0 := by
  simp [discardedWeight,dyadicWeight_zero_nonpos _ q hq]

theorem retainedWeight_nonneg (R q : ℝ) : 0 ≤ retainedWeight R q := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact (dyadicWeight_bounds n q).1
  · exact le_rfl

theorem discardedWeight_nonneg (R q : ℝ) : 0 ≤ discardedWeight R q := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact le_rfl
  · exact (dyadicWeight_bounds n q).1

theorem retainedWeight_bounds (R q : ℝ) : 0 ≤ retainedWeight R q ∧ retainedWeight R q ≤ 1 := by
  refine ⟨retainedWeight_nonneg R q,?_⟩
  by_cases hq : 0 < q
  · have hp := retained_add_discarded R q hq
    have hd := discardedWeight_nonneg R q
    linarith
  · rw [retainedWeight_zero_nonpos R q (le_of_not_gt hq)]; norm_num

theorem discardedWeight_bounds (R q : ℝ) : 0 ≤ discardedWeight R q ∧ discardedWeight R q ≤ 1 := by
  refine ⟨discardedWeight_nonneg R q,?_⟩
  by_cases hq : 0 < q
  · have hp := retained_add_discarded R q hq
    have hd := retainedWeight_nonneg R q
    linarith
  · rw [discardedWeight_zero_nonpos R q (le_of_not_gt hq)]; norm_num

theorem normValue_mul (v h : O) : normValue (v*h)=normValue v*normValue h := by
  simp only [normValue,← Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul]

end SevenEighths.CenteredMomentSectorLocalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstDiscardedEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstDiscardedEnergy
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson ConcretePrimeRowBridge
open CenteredMomentFirstReduced CenteredMomentSectorLocalization CenteredMomentCorrelation
open CenteredMomentCommonSupport CenteredMomentCanonicalFirst CenteredMomentSupportedCorrelation
open CenteredMomentFirstScale CenteredMomentActive
open CenteredMomentCompleteCommon IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

theorem tripleRow_norm_le_one (a b r : O) (ha : a≠0) (hb : b≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (hG : ∀ x,‖G x‖≤1) (z : O) :
    ‖tripleRow a b r χa χb G z‖≤1 := by
  let := finite_quotient_span ha
  let := finite_quotient_span hb
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  rw [tripleRow,norm_mul,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _)
      (QuadraticInitialBound.norm_finite_character_le_one χa _)).trans
      (QuadraticInitialBound.norm_finite_character_le_one χb _))).trans (hG _)

theorem tripleFourier_norm_le_full (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (hG : ∀ x,‖G x‖≤1) (h : O) :
    ‖tripleFourier a b r ha hb hr χa χb G h‖≤normValue (a*(b*r)) := by
  let := finite_quotient_span (mul_ne_zero ha (mul_ne_zero hb hr))
  let : Fintype (Residue (a*(b*r))) := Fintype.ofFinite _
  rw [tripleFourier,tsum_fintype]
  calc
    _ ≤ ∑ x : Residue (a*(b*r)),‖tripleResidue a b r χa χb G x*
      quotientTrace (a*(b*r)) (mul_ne_zero ha (mul_ne_zero hb hr)) (Ideal.Quotient.mk _ h*x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue (a*(b*r)),(1:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [norm_mul,(quotientTrace _ _).norm_apply,mul_one,tripleResidue_mk]
      exact tripleRow_norm_le_one a b r ha hb χa χb G hG z
    _ = _ := by simp [normValue,Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

theorem activeFunction_norm_le_one (I J : Ideal O) (hI : CanonicalQuadraticSieve.Supported I)
    (x : Residue (activeConductor I J)) : ‖activeFunction I J hI x‖≤1 := by
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
  calc
    _ = ‖finiteSexticRow (activePrime I J) (activeGood I J hI)
        (CenteredMomentCanonicalFirst.activeExponent I J) z‖ :=
      congrArg norm (principalSexticRow_mk (activePrime I J) (activeCoprime I J)
        (activeGood I J hI) (CenteredMomentCanonicalFirst.activeExponent I J)
        (activeConductor I J) (span_finitePrimeModulus _) z)
    _ ≤ 1 := QuadraticInitialBound.finiteSexticRow_norm_le_one _ _ _ z

end SevenEighths.CenteredMomentFirstDiscardedEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstTailAggregate
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstTailAggregate
open ActualEisensteinCubic HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstScale CenteredMomentSectorLocalization
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentTwist
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_norm_le_one (η : Character) (m A z : O) (t : ℝ)
    (I : Ideal O) (hI : I≠0) : ‖rowWeight η m A z t I‖≤1 := by
  have hp := norm_real_imaginary_power (Ideal.absNorm I:ℝ) t (norm_pos I hI)
  norm_cast at hp
  change ‖(idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)‖≤1
  rw [norm_mul,norm_mul,hp,mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (idealCoeff_norm_le_one η I)).trans (idealRowHom_norm _ _)

end SevenEighths.CenteredMomentFirstTailAggregate

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentExceptionalAmplitudePair
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentDetectorDictionary
open CenteredMomentExceptionalAllocationShell ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
universe u

lemma volume_pos {ι:Type u} [Fintype ι] (s:Data ι):0<volume s:=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

end SevenEighths.CenteredMomentExceptionalAmplitudePair

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstLocalization
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstLocalization
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentFirstDiscardedEnergy CenteredMomentSectorLocalization CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentFirstTailAggregate
open CanonicalQuadraticSieve HeckeFamily CenteredMomentHeckeExpansion CenteredMomentFirstEnergy
local notation "O" => ActualEisensteinCubic.O

theorem weighted_fourier_summable (W : 𝓢(ℝ,ℂ)) (k : ℝ) (hk : 0<k)
    (c w : O → ℂ) (B : ℝ) (hc : ∀ h,‖c h‖≤B) (hw : ∀ h,‖w h‖≤1) :
    Summable (fun h : O => w h*c h*paperRadialFourier W (k*normValue h)) := by
  have hs := paperRadialFourier_lattice_summable_norm W k hk
  simp_rw [← normValue_eq_embedding] at hs
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hs.mul_left B)
  intro h
  rw [norm_mul,norm_mul]
  exact mul_le_mul_of_nonneg_right
    ((mul_le_of_le_one_left (norm_nonneg _) (hw h)).trans (hc h)) (norm_nonneg _)

theorem retained_complex_norm (R q : ℝ) : ‖(retainedWeight R q:ℂ)‖≤1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (retainedWeight_nonneg R q)]
  exact (retainedWeight_bounds R q).2

theorem discarded_complex_norm (R q : ℝ) : ‖(discardedWeight R q:ℂ)‖≤1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (discardedWeight_nonneg R q)]
  exact (discardedWeight_bounds R q).2

theorem lattice_fourier_split (W : 𝓢(ℝ,ℂ)) (k : ℝ) (hk : 0<k)
    (c : O → ℂ) (B : ℝ) (hc : ∀ h,‖c h‖≤B) (R : ℝ) :
    (∑' h : O,c h*paperRadialFourier W (k*normValue h))=
      c 0*paperRadialFourier W 0+
        (∑' h : O,(retainedWeight R (normValue h):ℂ)*c h*paperRadialFourier W (k*normValue h))+
        (∑' h : O,(discardedWeight R (normValue h):ℂ)*c h*paperRadialFourier W (k*normValue h)) := by
  have hs := weighted_fourier_summable W k hk c (fun _ => 1) B hc (by simp)
  simp only [one_mul] at hs
  have hr := weighted_fourier_summable W k hk c (fun h => (retainedWeight R (normValue h):ℂ)) B hc
    (fun h => retained_complex_norm R _)
  have hd := weighted_fourier_summable W k hk c (fun h => (discardedWeight R (normValue h):ℂ)) B hc
    (fun h => discarded_complex_norm R _)
  rw [hs.tsum_eq_add_tsum_ite 0]
  have hzero : normValue (0:O)=0 := by simp [normValue]
  simp only [hzero,mul_zero]
  rw [add_assoc,← hr.tsum_add hd]
  congr 1
  apply tsum_congr
  intro h
  by_cases hh : h=0
  · subst h
    simp only [ite_true,hzero,
      retainedWeight_zero_nonpos R 0 le_rfl,discardedWeight_zero_nonpos R 0 le_rfl,
      Complex.ofReal_zero,zero_mul,add_zero]
  · rw [if_neg hh]
    have hp : 0<normValue h := norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr hh)
    have he : (retainedWeight R (normValue h):ℂ)+(discardedWeight R (normValue h):ℂ)=1 := by
      exact_mod_cast retained_add_discarded R (normValue h) hp
    rw [← add_mul,← add_mul,he,one_mul]

end SevenEighths.CenteredMomentFirstLocalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstSectorLocalization
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstSectorLocalization
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentFirstDiscardedEnergy CenteredMomentSectorLocalization CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentFirstTailAggregate
open CanonicalQuadraticSieve HeckeFamily CenteredMomentHeckeExpansion CenteredMomentFirstEnergy
local notation "O" => ActualEisensteinCubic.O

open CenteredMomentFirstLocalization

theorem reducedFirstSum_sector_split (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) (hK : 0<K) :
    reducedFirstSum I J hI hJ W K=canonicalZeroPair I J hI hJ W K+
      retainedPair I J hI hJ W K X Z ξ+discardedPair I J hI hJ W K X Z ξ := by
  unfold reducedFirstSum canonicalZeroPair retainedPair discardedPair
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  let Tsec:=firstNominalScale I J (∏ P∈E,P.val) K X
  dsimp only [canonicalZeroTerm,canonicalRetainedTerm,canonicalDiscardedTerm]
  simp_rw [← normValue_eq_embedding]
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  have ha : a≠0 := supported_element_ne_zero _ (residualGenerator_supported I J hI)
  have hb : b≠0 := supported_element_ne_zero _ (residualGenerator_supported J I hJ)
  have hr : r≠0 := finitePrimeModulus_ne_zero _
  have he : primeSubsetGenerator (fun P : CommonIndex I J => P.val) E≠0 := primeSubsetGenerator_ne_zero _ _
  have hk : 0<(K/normValue (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E))/normValue (a*(b*r)) :=
    div_pos (div_pos hK (norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr he)))
      (norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha (mul_ne_zero hb hr))))
  have hh := lattice_fourier_split W _ hk
    (tripleFourier a b r ha hb hr (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI))
    (normValue (a*(b*r)))
    (tripleFourier_norm_le_full a b r ha hb hr _ _ _ (activeFunction_norm_le_one I J hI))
    (frequencyRadius Tsec Z ξ)
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let k := (K/normValue e)/normValue (a*(b*r))
  let F := tripleFourier a b r ha hb hr (residualCharacter I J hI)
    (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
  let d := (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e
  change d*((k:ℂ)*∑' h : O,F h*paperRadialFourier W ((K/normValue e)*normValue h/normValue (a*(b*r))))=
    d*((k:ℂ)*(F 0*paperRadialFourier W 0))+
      d*((k:ℂ)*∑' h : O,(retainedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*F h*paperRadialFourier W (k*normValue h))+
      d*((k:ℂ)*∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*F h*paperRadialFourier W (k*normValue h))
  have heq (h : O) : (K/normValue e)*normValue h/normValue (a*(b*r))=k*normValue h := by dsimp [k];ring
  simp_rw [heq]
  rw [hh]
  ring

theorem finiteHeckeEnergy_sector_localized (η : Character) (m A : O) (t : ℝ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ))
    (K X Z ξ : ℝ) (hK : 0<K) :
    finiteHeckeEnergy η m A t S c W K=
      zeroEnergy η m A t S c W K+retainedEnergy η m A t S c W K X Z ξ+
        discardedEnergy η m A t S c W K X Z ξ := by
  rw [finiteHeckeEnergy_reduced_poisson η m A t hmLam hm2 S c W K hK]
  simp_rw [reducedFirstSum_sector_split _ _ _ _ W K X Z ξ hK,mul_add,Finset.sum_add_distrib]
  rfl

end SevenEighths.CenteredMomentFirstSectorLocalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ZeroMeanBridge
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentZeroMeanBridge
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentCommonSupport
open CenteredMomentFourier CenteredMomentCorrelation CenteredMomentSupportedCorrelation
open CenteredMomentSectorLocalization CenteredMomentFirstReduced CenteredMomentCanonicalFirst
open CenteredMomentActive CenteredMomentFirstDiscardedEnergy CenteredMomentFirstLocalization
local notation "O" => ActualEisensteinCubic.O

lemma normValue_ne_zero (a : O) (ha : a ≠ 0) : normValue a ≠ 0 :=
  by
    rw [normValue_eq_embedding]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero ha))

theorem quotientMean_pullback (a m : O) (ha : a ≠ 0) (hm : m ≠ 0)
    (h : a ∣ m) (F : Residue a → ℂ) :
    quotientMean m (fun x => F (frequencyReduction a m h x)) = quotientMean a F := by
  obtain ⟨b, rfl⟩ := h
  have hb : b ≠ 0 := right_ne_zero_of_mul hm
  have hh := conductorFourier_lift a b ha hb F 0
  simp only [mul_zero, conductorFourier, map_zero, zero_mul, AddChar.map_zero_eq_one,
    mul_one] at hh
  have he : frequencyReduction a (a*b) (dvd_mul_right a b) = conductorReduction a b := rfl
  unfold quotientMean
  rw [he, hh, normValue_mul, Complex.ofReal_mul]
  have ha' : (normValue a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (normValue_ne_zero a ha)
  have hb' : (normValue b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (normValue_ne_zero b hb)
  change ((normValue a : ℂ) * (normValue b : ℂ))⁻¹ *
    ((normValue b : ℂ) * _) = _
  field_simp

theorem dilationMask_sum (e d : O) (he : e ≠ 0) (F : Residue d → ℂ) :
    (∑' x : Residue (d*e), dilationMask e d F x) =
      ∑' y : Residue d, F (Ideal.Quotient.mk _ e * y) := by
  have hi := scaledResidue_injective d e (d*e) rfl he
  have hz (x : Residue (d*e)) (hx : x ∉ Set.range (scaledResidue d e (d*e) rfl)) :
      dilationMask e d F x = 0 := by
    obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [dilationMask_mk]
    split_ifs with h
    · obtain ⟨y,rfl⟩ := h
      exact False.elim (hx ⟨Ideal.Quotient.mk _ y, rfl⟩)
    · rfl
  have hs : Function.support (dilationMask e d F) ⊆ Set.range (scaledResidue d e (d*e) rfl) := by
    intro x hx
    by_contra hn
    exact hx (hz x hn)
  rw [← hi.tsum_eq hs]
  apply tsum_congr
  intro y
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_mk, dilationMask_mk, if_pos (dvd_mul_right e z), map_mul]

theorem quotientMean_dilation (e d : O) (he : e ≠ 0) (_hd : d ≠ 0)
    (F : Residue d → ℂ) (hF : ∀ x y, F (x*y) = F x * F y) :
    quotientMean (d*e) (dilationMask e d F) =
      (normValue e : ℂ)⁻¹ * F (Ideal.Quotient.mk _ e) * quotientMean d F := by
  rw [quotientMean, dilationMask_sum e d he]
  simp_rw [hF]
  rw [tsum_mul_left, normValue_mul, Complex.ofReal_mul, quotientMean]
  ring

theorem quotientMean_finite_sum {ι : Type*} [Fintype ι]
    (a : O) (ha : a ≠ 0) (F : Residue a → ℂ)
    (d : ι → O) (hd : ∀ i, d i ≠ 0) (G : (i : ι) → Residue (d i) → ℂ)
    (c : ι → ℂ)
    (h : ∀ z : O, F (Ideal.Quotient.mk _ z) =
      ∑ i, c i * G i (Ideal.Quotient.mk _ z)) :
    quotientMean a F = ∑ i, c i * quotientMean (d i) (G i) := by
  let m := a * ∏ i, d i
  have hm : m ≠ 0 := mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr (fun i _ => hd i))
  have haM : a ∣ m := dvd_mul_right _ _
  have hdM (i : ι) : d i ∣ m := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem d (Finset.mem_univ i)) a
  let := finite_quotient_span hm
  let : Fintype (Residue m) := Fintype.ofFinite _
  rw [← quotientMean_pullback a m ha hm haM F]
  have hh (x : Residue m) : F (frequencyReduction a m haM x) =
      ∑ i, c i * G i (frequencyReduction (d i) m (hdM i) x) := by
    obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa only [frequencyReduction_mk] using h z
  simp_rw [quotientMean, hh, tsum_fintype]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hl := quotientMean_pullback (d i) m (hd i) hm (hdM i) (G i)
  rw [quotientMean, tsum_fintype] at hl
  rw [← Finset.mul_sum, mul_left_comm, hl]
  rfl

theorem row_mask_expansion {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (z : O) (v : ℂ) :
    rowCoprimeMask P S z * v =
      ∑ E ∈ S.powerset, (UniqueFactorizationMonoid.moebius (∏ i∈E,P i) : ℂ) *
        (if primeSubsetGenerator P E ∣ z then v else 0) := by
  rw [rowCoprimeMask_subsets, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro E hE
  have hp (i : ι) : Prime (P i) := Ideal.prime_of_isPrime (NeZero.ne _) inferInstance
  rw [prime_product_moebius P hp hinj E]
  have he : primeSubsetGenerator P E ∣ z ↔ ∀ i ∈ E, z ∈ P i := by
    rw [← Ideal.mem_span_singleton, primeSubsetGenerator, span_idealGenerator,
      mem_prime_product_iff P hinj E z]
  rw [he]
  split_ifs <;> ring

theorem quotientMean_mask_expansion {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (a d : O) (ha : a ≠ 0) (hd : d ≠ 0)
    (F : Residue a → ℂ) (G : Residue d → ℂ)
    (hG : ∀ x y, G (x*y) = G x * G y)
    (hFG : ∀ z : O, F (Ideal.Quotient.mk _ z) =
      rowCoprimeMask P S z * G (Ideal.Quotient.mk _ z)) :
    quotientMean a F =
      ∑ E ∈ S.powerset, (UniqueFactorizationMonoid.moebius (∏ i∈E,P i) : ℂ) *
        (normValue (primeSubsetGenerator P E) : ℂ)⁻¹ *
          G (Ideal.Quotient.mk _ (primeSubsetGenerator P E)) * quotientMean d G := by
  have h := quotientMean_finite_sum a ha F
    (fun E : S.powerset => d * primeSubsetGenerator P E.val)
    (fun E => mul_ne_zero hd (primeSubsetGenerator_ne_zero P E.val))
    (fun E => dilationMask (primeSubsetGenerator P E.val) d G)
    (fun E => (UniqueFactorizationMonoid.moebius (∏ i∈E.val,P i) : ℂ)) (by
      intro z
      rw [hFG, row_mask_expansion P hinj S z]
      simp only [dilationMask_mk]
      exact (Finset.sum_coe_sort S.powerset _).symm)
  simp_rw [quotientMean_dilation _ _ (primeSubsetGenerator_ne_zero P _) hd G hG] at h
  simp only [← mul_assoc] at h
  exact h.trans (Finset.sum_coe_sort S.powerset (fun E : Finset ι =>
    (UniqueFactorizationMonoid.moebius (∏ i∈E,P i) : ℂ) *
      (normValue (primeSubsetGenerator P E) : ℂ)⁻¹ *
        G (Ideal.Quotient.mk _ (primeSubsetGenerator P E)) * quotientMean d G))

theorem tripleResidue_mul (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ)
    (hG : ∀ x y, G (x*y) = G x * G y) (x y : Residue (a*(b*r))) :
    tripleResidue a b r χa χb G (x*y) =
      tripleResidue a b r χa χb G x * tripleResidue a b r χa χb G y := by
  obtain ⟨u,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨v,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, tripleResidue_mk, tripleResidue_mk, tripleResidue_mk]
  exact tripleRow_mul a b r χa χb G hG u v

theorem original_pair_reduced_mask (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (z : O) :
    idealRowHom z I * star (idealRowHom z J) =
      rowCoprimeMask (fun P : CommonIndex I J => P.val)
        (principalSupport Finset.univ (leftExponent I J) (rightExponent I J)) z *
      tripleRow (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) z := by
  rw [original_pair_factor I J hI hJ]
  rw [common_ideal_pair_active (fun P : CommonIndex I J => P.val) (common_good I J hI)
    (common_odd I J hI) Finset.univ (leftExponent I J) (rightExponent I J)
    (fun P _ => (leftExponent_pos I J P).ne') (fun P _ => (rightExponent_pos I J P).ne')]
  have hactive : activeFunction I J hI (Ideal.Quotient.mk _ z) =
      finiteSexticRow (activePrime I J) (activeGood I J hI)
        (CenteredMomentCanonicalFirst.activeExponent I J) z :=
    principalSexticRow_mk (activePrime I J) (activeCoprime I J) (activeGood I J hI)
      (CenteredMomentCanonicalFirst.activeExponent I J) (activeConductor I J)
      (span_finitePrimeModulus _) z
  simp only [tripleRow, hactive]
  convert (preTransparency := .instances) mul_left_comm
    ((residualCharacter I J hI) (Ideal.Quotient.mk _ z) *
      (residualCharacter J I hJ)⁻¹ (Ideal.Quotient.mk _ z))
    (rowCoprimeMask (fun P : CommonIndex I J => P.val)
      (principalSupport Finset.univ (leftExponent I J) (rightExponent I J)) z)
    (finiteSexticRow (activePrime I J) (activeGood I J hI)
      (CenteredMomentCanonicalFirst.activeExponent I J) z) using 1
  congr 2

theorem original_pair_mean (I J : Ideal O) (hI : Supported I) (hJ : Supported J) :
    let hi : Supported (Ideal.span {CompletedGauss.primaryGenerator I}) :=
      (CenteredMomentSourceRow.primary_span_supported I hI).symm ▸ hI
    let hj : Supported (Ideal.span {CompletedGauss.primaryGenerator J}) :=
      (CenteredMomentSourceRow.primary_span_supported J hJ).symm ▸ hJ
    quotientMean (CompletedGauss.primaryGenerator I * CompletedGauss.primaryGenerator J)
      (CenteredMomentRowNorm.pairResidue _ _ hi hj) =
    ∑ E ∈ inactiveSubsets I J,
      (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val) : ℂ) *
        (normValue (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) : ℂ)⁻¹ *
      tripleRow (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
        (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) *
      quotientMean (residualGenerator I J * (residualGenerator J I * activeConductor I J))
        (tripleResidue (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)) := by
  dsimp only
  have h := quotientMean_mask_expansion (fun P : CommonIndex I J => P.val) Subtype.val_injective
    (principalSupport Finset.univ (leftExponent I J) (rightExponent I J))
    (CompletedGauss.primaryGenerator I * CompletedGauss.primaryGenerator J)
    (residualGenerator I J * (residualGenerator J I * activeConductor I J))
    (mul_ne_zero (supported_primaryGenerator_ne_zero I hI) (supported_primaryGenerator_ne_zero J hJ))
    (mul_ne_zero (supported_element_ne_zero _ (residualGenerator_supported I J hI))
      (mul_ne_zero (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
        (finitePrimeModulus_ne_zero _)))
    (CenteredMomentRowNorm.pairResidue _ _
      ((CenteredMomentSourceRow.primary_span_supported I hI).symm ▸ hI)
      ((CenteredMomentSourceRow.primary_span_supported J hJ).symm ▸ hJ))
    (tripleResidue (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
      (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI))
    (tripleResidue_mul _ _ _ _ _ _ (principalSexticRow_mul _ _ _ _ _ _)) (by
      intro z
      rw [CenteredMomentRowNorm.pairResidue_mk, CenteredMomentSourceRow.primary_span_supported I hI,
        CenteredMomentSourceRow.primary_span_supported J hJ, tripleResidue_mk]
      exact original_pair_reduced_mask I J hI hJ z)
  simpa only [inactiveSubsets, tripleResidue_mk] using h

theorem canonicalZeroTerm_eq_mean (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalZeroTerm I J hI hJ E W K = (K : ℂ) *
      ((UniqueFactorizationMonoid.moebius (∏ P∈E,P.val) : ℂ) *
        (normValue (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) : ℂ)⁻¹ *
      tripleRow (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
        (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) *
      quotientMean (residualGenerator I J * (residualGenerator J I * activeConductor I J))
        (tripleResidue (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI))) *
      paperRadialFourier W 0 := by
  simp only [canonicalZeroTerm, tripleFourier, map_zero, zero_mul,
    AddChar.map_zero_eq_one, mul_one, quotientMean, div_eq_mul_inv,
    Complex.ofReal_mul, Complex.ofReal_inv]
  ring

theorem canonicalZeroPair_eq_original (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let hi : Supported (Ideal.span {CompletedGauss.primaryGenerator I}) :=
      (CenteredMomentSourceRow.primary_span_supported I hI).symm ▸ hI
    let hj : Supported (Ideal.span {CompletedGauss.primaryGenerator J}) :=
      (CenteredMomentSourceRow.primary_span_supported J hJ).symm ▸ hJ
    canonicalZeroPair I J hI hJ W K =
      (((K / ‖eisEmbedding (CompletedGauss.primaryGenerator I * CompletedGauss.primaryGenerator J)‖^2 : ℝ) : ℂ) *
        CenteredMomentRowNorm.pairFourier (CompletedGauss.primaryGenerator I) (CompletedGauss.primaryGenerator J)
          hi hj 0) * paperRadialFourier W 0 := by
  dsimp only
  rw [canonicalZeroPair]
  simp_rw [canonicalZeroTerm_eq_mean]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← original_pair_mean I J hI hJ]
  rw [CenteredMomentZeroMode.pairFourier_zero, quotientMean, ← normValue_eq_embedding,
    Complex.ofReal_div, div_eq_mul_inv]
  ring

theorem quotientMean_congr (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (F : Residue a → ℂ) (G : Residue b → ℂ)
    (h : ∀ z : O, F (Ideal.Quotient.mk _ z) = G (Ideal.Quotient.mk _ z)) :
    quotientMean a F = quotientMean b G := by
  have hh := quotientMean_finite_sum a ha F (fun _ : Unit => b) (fun _ => hb)
    (fun _ => G) (fun _ => (1 : ℂ)) (by intro z; simpa using h z)
  simpa using hh

theorem scaled_pairFourier_eq_mean (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) (K : ℝ) :
    (((K / ‖eisEmbedding (a*b)‖^2 : ℝ) : ℂ) * CenteredMomentRowNorm.pairFourier a b ha hb 0) =
      (K : ℂ) * quotientMean (a*b) (CenteredMomentRowNorm.pairResidue a b ha hb) := by
  rw [CenteredMomentZeroMode.pairFourier_zero, quotientMean, ← normValue_eq_embedding,
    Complex.ofReal_div, div_eq_mul_inv]
  ring

theorem canonicalZeroPair_eq_generators (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (haI : Ideal.span {a} = I) (hbJ : Ideal.span {b} = J) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalZeroPair I J hI hJ W K =
      (((K / ‖eisEmbedding (a*b)‖^2 : ℝ) : ℂ) * CenteredMomentRowNorm.pairFourier a b ha hb 0) *
        paperRadialFourier W 0 := by
  rw [canonicalZeroPair_eq_original, scaled_pairFourier_eq_mean, scaled_pairFourier_eq_mean]
  congr 2
  apply quotientMean_congr
    _ _ (mul_ne_zero (supported_primaryGenerator_ne_zero I hI) (supported_primaryGenerator_ne_zero J hJ))
    (mul_ne_zero (supported_element_ne_zero a ha) (supported_element_ne_zero b hb))
  intro z
  simp only [CenteredMomentRowNorm.pairResidue_mk, CenteredMomentSourceRow.primary_span_supported I hI,
    CenteredMomentSourceRow.primary_span_supported J hJ, haI, hbJ]

theorem canonical_ideal_zero_sum (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑ I : S, ∑ J : S, (c I.val * star (c J.val)) *
      canonicalZeroPair I.val J.val (hS I.val I.property) (hS J.val J.property) W K) =
      CenteredMomentZeroMode.idealZeroEnergy S hS c K * paperRadialFourier W 0 := by
  rw [CenteredMomentZeroMode.idealZeroEnergy]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [canonicalZeroPair_eq_generators I.val J.val (hS I.val I.property) (hS J.val J.property)
    (CenteredMomentZeroMode.idealColumn S I) (CenteredMomentZeroMode.idealColumn S J)
    (CenteredMomentZeroMode.idealColumn_supported S hS I) (CenteredMomentZeroMode.idealColumn_supported S hS J)
    (CenteredMomentZeroMode.idealColumn_span S I) (CenteredMomentZeroMode.idealColumn_span S J)]
  ring

theorem zeroEnergy_eq_original (η : HeckeFamily.Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    zeroEnergy η m A t S c W K =
      CenteredMomentZeroMode.idealZeroEnergy (CenteredMomentSourceRow.supportedColumns S)
        (fun _ h => (Finset.mem_filter.mp h).2)
        (fun I => c I * CenteredMomentHeckeExpansion.rowWeight η m A 1 t I) K * paperRadialFourier W 0 := by
  unfold zeroEnergy
  exact canonical_ideal_zero_sum (CenteredMomentSourceRow.supportedColumns S)
    (fun _ h => (Finset.mem_filter.mp h).2)
    (fun I => c I * CenteredMomentHeckeExpansion.rowWeight η m A 1 t I) W K

end SevenEighths.CenteredMomentZeroMeanBridge

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SupportedZeroEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSupportedZeroEnergy
open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve CanonicalRowCompletion IdealMobiusDivisorSum
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentZeroMode
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentFirstLocalization
open CenteredMomentZeroMeanBridge EisensteinSchwartzPoisson HeckeFamily
local notation "O" => ActualEisensteinCubic.O

theorem idealZeroEnergy_filter (S : Finset (Ideal O)) (hS : ∀ I∈S,Supported I)
    (c : Ideal O → ℂ) (K : ℝ) (p : Ideal O → Prop) [DecidablePred p]
    (hc : ∀ I∈S, ¬p I → c I=0) :
    idealZeroEnergy S hS c K =
      idealZeroEnergy (S.filter p) (fun I h => hS I (Finset.mem_filter.mp h).1) c K := by
  let e : S.filter p → S := fun I => ⟨I.val,(Finset.mem_filter.mp I.property).1⟩
  let ep : (S.filter p) × (S.filter p) → S × S := fun q => (e q.1,e q.2)
  have he : Function.Injective e := by
    intro I J h
    apply Subtype.ext
    exact congrArg (fun x : S => x.val) h
  have hep : Function.Injective ep := by
    intro q r h
    exact Prod.ext (he (congrArg Prod.fst h)) (he (congrArg Prod.snd h))
  let f : S × S → ℂ := fun q => (c q.1.val * star (c q.2.val)) *
    (((K / ‖eisEmbedding (idealColumn S q.1 * idealColumn S q.2)‖^2 : ℝ) : ℂ) *
      CenteredMomentRowNorm.pairFourier (idealColumn S q.1) (idealColumn S q.2)
        (idealColumn_supported S hS q.1) (idealColumn_supported S hS q.2) 0)
  have hs : Function.support f ⊆ Set.range ep := by
    intro q hq
    have hi : p q.1.val := by
      by_contra hn
      exact hq (by simp only [f,hc q.1.val q.1.property hn,zero_mul])
    have hj : p q.2.val := by
      by_contra hn
      exact hq (by simp only [f,hc q.2.val q.2.property hn,star_zero,mul_zero,zero_mul])
    exact ⟨(⟨q.1.val,Finset.mem_filter.mpr ⟨q.1.property,hi⟩⟩,
      ⟨q.2.val,Finset.mem_filter.mpr ⟨q.2.property,hj⟩⟩),rfl⟩
  have ht := hep.tsum_eq hs
  simpa only [tsum_fintype,Fintype.sum_prod_type,f,ep,e,idealZeroEnergy,idealColumn] using ht.symm

theorem zeroEnergy_eq_active_original (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    zeroEnergy η m A t S c W K =
      idealZeroEnergy (activeColumns S c) (activeColumns_supported S c)
        (fun I => c I*rowWeight η m A 1 t I) K * paperRadialFourier W 0 := by
  rw [zeroEnergy_eq_original]
  congr 1
  exact idealZeroEnergy_filter (supportedColumns S) (fun I h => (Finset.mem_filter.mp h).2)
    (fun I => c I*rowWeight η m A 1 t I) K (fun I => c I≠0)
    (fun I _ h => by simp only [not_not] at h; rw [h,zero_mul])

theorem finiteColumnCoefficient_witness {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (I : Ideal O)
    (hI : finiteColumnCoefficient S β I≠0) :
    ∃ v∈S, β v≠0 ∧ finiteTupleProduct v=I := by
  obtain ⟨v,hv,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hI
  exact ⟨v,(Finset.mem_filter.mp hv).1,hne,(Finset.mem_filter.mp hv).2⟩

theorem finite_tuple_fiber_card {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (I : Ideal O) (hI : I≠0) :
    (S.filter (fun v => finiteTupleProduct v=I)).card ≤
      (idealDivisors I).card^(Fintype.card ι+2) := by
  let T := S.filter (fun v => finiteTupleProduct v=I)
  let f (v : T) : (ι ⊕ Fin 2) → idealDivisors I := fun i => ⟨v.val i,by
    apply (mem_idealDivisors hI).mpr
    rw [← (Finset.mem_filter.mp v.property).2]
    exact Finset.dvd_prod_of_mem v.val (Finset.mem_univ i)⟩
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun he i)
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_sum,Fintype.card_fin,T]
    using Fintype.card_le_of_injective f hf

theorem finiteColumnCoefficient_norm_le {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (B : ℝ) (hB : 0≤B)
    (hβ : ∀ v∈S, finiteTupleProduct v≠0 → ‖β v‖≤B) (I : Ideal O) (hI : I≠0) :
    ‖finiteColumnCoefficient S β I‖ ≤ B*((idealDivisors I).card:ℝ)^(Fintype.card ι+2) := by
  calc
    _ ≤ ∑ v∈S.filter (fun v => finiteTupleProduct v=I),‖β v‖ := norm_sum_le _ _
    _ ≤ ∑ _v∈S.filter (fun v => finiteTupleProduct v=I),B := by
      apply Finset.sum_le_sum
      intro v hv
      exact hβ v (Finset.mem_filter.mp hv).1 ((Finset.mem_filter.mp hv).2 ▸ hI)
    _ = B*((S.filter (fun v => finiteTupleProduct v=I)).card:ℝ) := by simp; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact_mod_cast finite_tuple_fiber_card S I hI

theorem active_tuple_zero_energy_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (η : Character) (m A : O) (t : ℝ) (S : Finset (Tuple ι))
        (β : Tuple ι → ℂ) (W : 𝓢(ℝ,ℂ)) (X K B : ℝ),
      1≤X → 0≤K → 0≤B →
      (∀ v∈S,finiteTupleProduct v≠0 → ‖β v‖≤B) →
      (∀ I∈supportedColumns (finiteColumns S),finiteColumnCoefficient S β I≠0 →
        (Ideal.absNorm I:ℝ)≤X) →
      ‖zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) W K‖ ≤
        C*K*B^2*‖paperRadialFourier W 0‖*X^(1+ε) := by
  let δ := ε/(4*(N+2:ℕ))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hn : (N+2:ℝ)≠0 := by positivity
  have hδn : δ*(N+2:ℕ)=ε/4 := by dsimp [δ]; push_cast; field_simp
  obtain ⟨D,hD,hd⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  obtain ⟨C,hC,hc⟩ := ideal_zero_energy_bound (ε/2) (by positivity)
  refine ⟨C*((1+D)^(N+2))^2,by positivity,?_⟩
  intro ι _ hi η m A t S β W X K B hX hK hB hβ hN
  let c := finiteColumnCoefficient S β
  let Q := activeColumns (finiteColumns S) c
  have hQ : ∀ I∈Q,Supported I := activeColumns_supported _ _
  have hX0 : 0<X := zero_lt_one.trans_le hX
  have hNX (I : Ideal O) (hI : I∈Q) : (Ideal.absNorm I:ℝ)≤X :=
    hN I (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hI).2
  have hbase : 1≤(1+D)*X^δ := by
    have hxδ : 1≤X^δ := Real.one_le_rpow hX hδ.le
    nlinarith
  have hcoeff (I : Ideal O) (hI : I∈Q) :
      ‖c I*rowWeight η m A 1 t I‖ ≤ B*((1+D)^(N+2)*X^(ε/4)) := by
    have hI0 := (hQ I hI).1
    have hdI : ((idealDivisors I).card:ℝ) ≤ (1+D)*X^δ := by
      apply (hd I hI0).trans
      apply mul_le_mul (by linarith : D≤1+D)
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hNX I hI) hδ.le) (by positivity) (by positivity)
    have hp : ((1+D)*X^δ)^(N+2) = (1+D)^(N+2)*X^(ε/4) := by
      rw [mul_pow,←Real.rpow_mul_natCast hX0.le,hδn]
    rw [norm_mul]
    calc
      _ ≤ ‖c I‖*1 := mul_le_mul_of_nonneg_left
        (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η m A 1 t I hI0) (norm_nonneg _)
      _ = ‖c I‖ := mul_one _
      _ ≤ B*((idealDivisors I).card:ℝ)^(Fintype.card ι+2) :=
        finiteColumnCoefficient_norm_le S β B hB hβ I hI0
      _ ≤ B*((1+D)*X^δ)^(Fintype.card ι+2) := by gcongr
      _ ≤ B*((1+D)*X^δ)^(N+2) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (by omega)) hB
      _ = _ := by rw [hp]
  have hb := hc Q hQ (fun I => c I*rowWeight η m A 1 t I)
    X K (B*((1+D)^(N+2)*X^(ε/4))) hX hK (by positivity) hNX hcoeff
  rw [zeroEnergy_eq_active_original,norm_mul]
  apply (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans_eq
  have hxpow : (X^(ε/4))^2*X^(1+ε/2)=X^(1+ε) := by
    rw [←Real.rpow_mul_natCast hX0.le,←Real.rpow_add hX0]
    congr 1
    ring
  calc
    _ = C*((1+D)^(N+2))^2*K*B^2*‖paperRadialFourier W 0‖*
      ((X^(ε/4))^2*X^(1+ε/2)) := by ring
    _ = _ := by rw [hxpow]

end SevenEighths.CenteredMomentSupportedZeroEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceZeroEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSourceZeroEnergy
open ActualEisensteinCubic HeckeFamily CenteredMomentRectangle
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentSupportedZeroEnergy
open CenteredMomentFirstLocalization CenteredMomentSourceRow
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

theorem profileCoefficient_norm_le {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (hν : ∀ j I,‖ν j I‖≤1)
    (Wslot : ι → ℝ → ℂ) (P D : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (D₁ D₂ : ℝ)
    (hD : ∀ j,0≤D j) (hD₁ : 0≤D₁) (hD₂ : 0≤D₂)
    (hslot : ∀ j x,‖Wslot j x‖≤D j)
    (h₁ : ∀ x,‖W₁ x‖≤D₁) (h₂ : ∀ x,‖W₂ x‖≤D₂)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    ‖profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖≤
      2*D₁*D₂*(∏ j,D j) := by
  have hp : ‖∏ j,ν j (v (Sum.inl j))*Wslot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/P j)‖≤∏ j,D j := by
    rw [norm_prod]
    apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    intro j _
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (hν j _) (hslot j _)
      (norm_nonneg _) zero_le_one
  have hr (I J : Ideal O) : ‖idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J‖≤2*D₁*D₂ := by
    unfold idealRectangle
    apply (norm_sub_le _ _).trans
    rw [norm_mul,norm_mul]
    have hx := mul_le_mul (h₁ ((Ideal.absNorm I:ℝ)/X₁))
      (h₂ ((Ideal.absNorm J:ℝ)/X₂)) (norm_nonneg _) hD₁
    have hy := mul_le_mul (h₁ ((Ideal.absNorm I:ℝ)/Y₁))
      (h₂ ((Ideal.absNorm J:ℝ)/Y₂)) (norm_nonneg _) hD₁
    linarith
  have hm (p : Prop) [Decidable p] : ‖(if p then 1 else 0 : ℂ)‖≤1 := by
    split_ifs <;> norm_num
  have hDp : 0≤∏ j,D j := Finset.prod_nonneg (fun j _ => hD j)
  unfold profileCoefficient
  rw [norm_mul,norm_mul,norm_mul]
  have h := mul_le_mul
    (mul_le_mul (mul_le_mul hp (hm (IsCoprime (finiteTupleProduct v) R)) (norm_nonneg _) (Finset.prod_nonneg (fun j _ => hD j)))
      (hr (B₁*v (Sum.inr 0)) (B₂*v (Sum.inr 1))) (norm_nonneg _) (by positivity))
    (hm (s∣finiteTupleProduct v)) (norm_nonneg _) (by positivity)
  simpa only [mul_one] using h.trans_eq (by ring)

theorem profileCoefficient_product_bound {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ)
    (P b : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ)
    (B₁ B₂ s : Ideal O)
    (hP : ∀ j,0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hz : ∀ j,Wslot j 0=0) (hz₁ : W₁ 0=0) (hz₂ : W₂ 0=0)
    (hs : ∀ j x,Wslot j x≠0 → x≤b j)
    (hs₁ : ∀ x,W₁ x≠0 → x≤b₁) (hs₂ : ∀ x,W₂ x≠0 → x≤b₂)
    (v : Tuple ι)
    (hv : profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    finiteTupleProduct v≠0 ∧ (Ideal.absNorm (finiteTupleProduct v):ℝ)≤
      (∏ j,b j)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  let e := Fintype.equivFin ι
  have hzero : ∀ i,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i 0=0 := by
    simpa only [Fin.forall_fin_add,sourceProfiles,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hz (e.symm j)) (And.intro hz₁ hz₂)
  have hsup : ∀ i x,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i x≠0 →
      x≤ sourceBounds (fun j => b (e.symm j)) b₁ b₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hs (e.symm j)) (And.intro hs₁ hs₂)
  have hn : CenteredMomentAddedZero.originalCoefficient (Fintype.card ι) 1
      (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0
      (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j)) (fun j => P (e.symm j))
      W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (tupleEquiv e v)≠0 := by
    rw [originalCoefficient_reindex,←profileCoefficient_eq_original]
    exact hv
  have hh := originalCoefficient_product_bound (Fintype.card ι) 1
    (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0 (fun j => ν (e.symm j))
    (fun j => Wslot (e.symm j)) (fun j => P (e.symm j)) (fun j => b (e.symm j))
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j => hP (e.symm j))
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hzero hsup (tupleEquiv e v) hn
  simpa only [tupleProduct_reindex,sourceRadius,e.symm.prod_comp] using hh

theorem zeroEnergy_eq_zero_of_subunit {ι : Type*} [Fintype ι]
    (η : Character) (m A : O) (t : ℝ) (S : Finset (Tuple ι)) (β : Tuple ι → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K Y : ℝ) (hY : Y<1)
    (hN : ∀ v∈S,β v≠0 → finiteTupleProduct v≠0 ∧
      (Ideal.absNorm (finiteTupleProduct v):ℝ)≤Y) :
    zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) W K=0 := by
  have hb (v : Tuple ι) (hv : v∈S) : β v=0 := by
    by_contra hn
    have hh := hN v hv hn
    have hnorm : (1:ℝ)≤Ideal.absNorm (finiteTupleProduct v) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hh.1)
    linarith
  have hc (I : Ideal O) : finiteColumnCoefficient S β I=0 := by
    unfold finiteColumnCoefficient
    exact Finset.sum_eq_zero (fun v hv => hb v (Finset.mem_filter.mp hv).1)
  simp only [zeroEnergy,hc,zero_mul,star_zero,mul_zero,Finset.sum_const_zero]

end SevenEighths.CenteredMomentSourceZeroEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceInputTailUniform
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentSourceInputTailUniform
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceZeroEnergy CenteredMomentSourceLiveColumn CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMass
open CenteredMomentSupportedTailAggregate CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentSourceInputTailUniform.instDecidableEqSumFinOfNatNat_solutions
omit [DecidableEq ι] in
lemma plainControl_nonneg (s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)):0≤plainControl s W₁ W₂:=by
  unfold plainControl
  exact mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun i _=>(s.M_ge_one i).trans' zero_le_one))
    (apply_nonneg _ _)) (apply_nonneg _ _)

omit [DecidableEq ι] in
lemma volume_pos (s:Input ι):0<volume s.toData:=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

end SevenEighths.CenteredMomentSourceInputTailUniform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceInputZeroUniform
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSourceInputZeroUniform
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceZeroEnergy CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMass CenteredMomentSourceInputTailUniform
open CenteredMomentFirstLocalization EisensteinSchwartzPoisson
open CenteredMomentExceptionalAmplitudePair CenteredMomentAddedZeroUniform
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentSourceInputZeroUniform.instDecidableEqSumFinOfNatNat_definitions
omit [DecidableEq ι] in
theorem first_input_zero_bound (hi:ι→ℝ)(wlo whi ε:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(_hwhi:0≤whi)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0≤K→
      ‖zeroEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*K*‖paperRadialFourier Φ 0‖*(volume s.toData)^ε:=by
  obtain ⟨C₀,hC₀,hbound⟩:=active_tuple_zero_energy_bound (Fintype.card ι) ε hε
  let L:=1+(∏i,hi i)*whi^2
  have hprod:0≤∏i,hi i:=Finset.prod_nonneg (fun i _=>hhi i)
  have hL:0<L:=by dsimp [L];positivity
  refine ⟨4*C₀*L^(1+ε),by positivity,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK
  let V:=volume s.toData
  have hV:0<V:=volume_pos s
  let β:=profileCoefficient R s.ν s.W s.P W₁ W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed
  have hc:coefficient s R seed=finiteColumnCoefficient (Fintype.piFinset s.pools) β:=by
    unfold coefficient;rw [he₁,he₂]
  have hcontrol:=plainControl_nonneg s W₁ W₂
  have hβ (v:Tuple ι):‖β v‖≤2*plainControl s W₁ W₂:=by
    have hb:=profileCoefficient_norm_le R s.ν s.ν_bound s.W s.P s.M W₁ W₂
      (SchwartzMap.seminorm ℝ 0 0 W₁) (SchwartzMap.seminorm ℝ 0 0 W₂)
      (fun i=>zero_le_one.trans (s.M_ge_one i)) (apply_nonneg _ _) (apply_nonneg _ _)
      s.W_bound (SchwartzMap.norm_le_seminorm ℝ W₁) (SchwartzMap.norm_le_seminorm ℝ W₂)
      s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v
    exact hb.trans_eq (by dsimp [plainControl];ring)
  have hz (i:ι):s.W i 0=0:=by
    by_contra hn
    exact (not_le_of_gt (s.lo_pos i)) (s.support i hn).1
  have hzW (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc wlo whi):W 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (hs hn).1
  have hN (v:Tuple ι)(hv:β v≠0):finiteTupleProduct v≠0 ∧
      (Ideal.absNorm (finiteTupleProduct v):ℝ)≤L*V:=by
    have hp:=profileCoefficient_product_bound R s.ν s.W s.P hi W₁ W₂ whi whi
      s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed
      s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos one_ne_zero one_ne_zero rfl s.same_product
      hz (hzW W₁ hs₁) (hzW W₂ hs₂) (fun i x hx=>((s.support i hx).2).trans (hshi i))
      (fun x hx=>(hs₁ hx).2) (fun x hx=>(hs₂ hx).2) v hv
    refine ⟨hp.1,hp.2.trans ?_⟩
    simp only [map_one,Nat.cast_one,one_mul,div_one]
    change (∏i,hi i)*whi*whi*(s.X₁*s.X₂)*(∏i,s.P i)≤_
    have hh:0≤V:=hV.le
    dsimp [L,V,volume] at *
    nlinarith
  rw [hc]
  by_cases hsmall:L*V<1
  · rw [zeroEnergy_eq_zero_of_subunit s.η m A s.t (Fintype.piFinset s.pools) β Φ K
      (L*V) hsmall (fun v _ hv=>hN v hv),norm_zero,zero_div]
    positivity
  have hb:=hbound (le_refl (Fintype.card ι)) s.η m A s.t (Fintype.piFinset s.pools) β Φ
    (L*V) K (2*plainControl s W₁ W₂) (le_of_not_gt hsmall) hK (by positivity)
    (fun v _ _=>hβ v) (fun I _ hI=>by
      obtain ⟨v,hv,hn,he⟩:=finiteColumnCoefficient_witness _ _ I hI
      rw [←he];exact (hN v hn).2)
  apply (div_le_div_of_nonneg_right hb hV.le).trans_eq
  have hp:(L*V)^(1+ε)/V=L^(1+ε)*V^ε:=by
    rw [Real.mul_rpow hL.le hV.le,Real.rpow_add hV,Real.rpow_one]
    field_simp
  change C₀*K*(2*plainControl s W₁ W₂)^2*‖paperRadialFourier Φ 0‖*(L*V)^(1+ε)/V=_
  calc
    _=4*C₀*(plainControl s W₁ W₂)^2*K*‖paperRadialFourier Φ 0‖*((L*V)^(1+ε)/V):=by ring
    _=_:=by rw [hp];ring

omit [DecidableEq ι] in
theorem first_input_zero_uniform (hi:ι→ℝ)(wlo whi ε:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hε:0<ε):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0≤K→
      ‖zeroEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*
        (volume s.toData)^ε:=by
  obtain ⟨C₀,hC₀,hb⟩:=first_input_zero_bound hi wlo whi ε hhi hwlo hwhi hε
  obtain ⟨SΦ,D,hD,hd⟩:=paperRadialFourier_euler_source_weighted_bound 0 0
  refine ⟨SΦ,C₀*D,mul_pos hC₀ hD,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK
  have hf:‖paperRadialFourier Φ 0‖≤D*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ:=by
    simpa only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,pow_zero,one_mul,zero_mul] using
      hd Φ 0 le_rfl 0 le_rfl
  have hVp:0≤(volume s.toData)^ε:=Real.rpow_nonneg (volume_pos s).le _
  apply (hb s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK).trans
  calc
    _≤C₀*(plainControl s W₁ W₂)^2*K*(D*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)*
        (volume s.toData)^ε:=by gcongr
    _=_:=by ring

omit [DecidableEq ι] in
theorem first_input_zero_capped (hi:ι→ℝ)(wlo whi B ε:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀Z:ℝ,1≤Z→
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→volume s.toData≤Z^B→
      ∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0≤K→
      ‖zeroEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε:=by
  let δ:=ε/(B+1)
  have hδ:0<δ:=div_pos hε (by linarith)
  obtain ⟨SΦ,C,hC,hb⟩:=first_input_zero_uniform hi wlo whi δ hhi hwlo hwhi hδ
  refine ⟨SΦ,C,hC,?_⟩
  intro Z hZ s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi hV m A R seed Φ K hK
  have hp:(volume s.toData)^δ≤Z^ε:=by
    calc
      _≤(Z^B)^δ:=Real.rpow_le_rpow (volume_pos s).le hV hδ.le
      _=Z^(B*δ):=(Real.rpow_mul (zero_le_one.trans hZ) B δ).symm
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZ (by
        have hh:δ*(B+1)=ε:=by dsimp [δ];field_simp
        nlinarith)
  exact (hb s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK).trans
    (mul_le_mul_of_nonneg_left hp (by positivity))

end SevenEighths.CenteredMomentSourceInputZeroUniform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceInputFirstRemainder
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentSourceInputFirstRemainder
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceInputTailUniform
open CenteredMomentSourceInputZeroUniform CenteredMomentSourceInputFirstSectorTail
open CenteredMomentFirstEnergy EisensteinSchwartzPoisson
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentSourceInputFirstRemainder.instDecidableEqSumFinOfNatNat_definitions
omit [DecidableEq ι] in
theorem original_first_remainder_oai (hi:ι→ℝ)(wlo whi B ε ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧ 0<Ctail ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),
      s.W₁=W₁→s.W₂=W₂→Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤hi i)→
      ∀(m A:O),ConcretePrimeRowBridge.goodLambda∣m→(2:O)∣m→
      ∀(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0<K→
      volume s.toData≤Z^B→K⁻¹≤Z^B→
      ‖finiteHeckeEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
          (coefficient s R seed) Φ K-
        CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A s.t
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed) Φ K
          (volume s.toData) Z ξ‖/volume s.toData≤
      Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε+
      Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨Sdiag,Cdiag,hCdiag,hdiag⟩:=first_input_zero_capped hi wlo whi B ε hhi hwlo hwhi hB hε
  obtain ⟨Stail,Ctail,hCtail,htail⟩:=local_input_tail hi wlo whi B ξ saving hhi hwlo hwhi hB hξ
  refine ⟨Sdiag,Stail,Cdiag,Ctail,hCdiag,hCtail,?_⟩
  filter_upwards [htail] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A hml hm2 R seed Φ K hK hVcap hKi
  have hd:=hdiag Z hZ.1.le s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi hVcap m A R seed Φ K hK.le
  have ht:=hZ.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK hVcap hKi
  rw [CenteredMomentFirstSectorLocalization.finiteHeckeEnergy_sector_localized
    s.η m A s.t hml hm2 (finiteColumns (Fintype.piFinset s.pools))
    (coefficient s R seed) Φ K (volume s.toData) Z ξ hK]
  rw [show ∀a b c:ℂ,a+b+c-b=a+c by intros;ring]
  exact ((div_le_div_of_nonneg_right (norm_add_le _ _) (volume_pos s).le).trans_eq
    (add_div _ _ _)).trans (add_le_add hd ht)

end SevenEighths.CenteredMomentSourceInputFirstRemainder

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.CenteredMomentSourceInputFirstRemainder.original_first_remainder_oai.{u_1} := @OAI.SevenEighths.CenteredMomentSourceInputFirstRemainder.original_first_remainder_oai.{u_1}
