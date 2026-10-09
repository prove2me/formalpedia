-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentNaturalReflection.original_inverse_reflection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T01:40:54.183764+00:00
-- url     : https://prove2.me/submissions/913d1f7e-d1d0-4466-bf8a-b0569556aebf

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B016
import Theorems.Thm_OAI_SmoothMobiusCorrection_prime_norm_two_le

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ConductorPresentation
namespace OAI

namespace SevenEighths

namespace FiniteConductor

variable {R : Type*} [CommRing R] [Finite R]

theorem FactorsThroughIdeal.bot (χ : MulChar R ℂ) : FactorsThroughIdeal χ ⊥ := by
  rw [factorsThroughIdeal_iff]
  intro u hu
  have hu1 : (u : R) = 1 := sub_eq_zero.mp hu
  rw [hu1, map_one]

end FiniteConductor

namespace ConductorPresentation

open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open scoped Classical

noncomputable section

variable {A : Type*} [CommRing A] [IsDedekindDomain A] [Infinite A]
  [Module.Free ℤ A] [Module.Finite ℤ A]

theorem exists_primitive_presentation (M : Ideal A) [Finite (A ⧸ M)]
    (χ : MulChar (A ⧸ M) ℂ) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      M ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ M.absNorm ∧
      ∀ a : A, χ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 := by
  obtain ⟨K, φ, hMK, hbotK, hK, hprimitive, hnorm, hmask⟩ :=
    exists_primitive_presentation_above_quotient M χ ⊥ (FactorsThroughIdeal.bot χ)
  refine ⟨K, φ, hMK, hK, hprimitive, ?_, hmask⟩
  simpa only [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using hnorm

end

end ConductorPresentation

end SevenEighths

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Continuation
namespace OAI

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace SevenEighths.Continuation

theorem product_identity_on_halfPlane (a b : ℝ) (L M W : ℂ → ℂ)
    (hL : AnalyticOnNhd ℂ L {s : ℂ | a < s.re})
    (hM : AnalyticOnNhd ℂ M {s : ℂ | a < s.re})
    (hW : AnalyticOnNhd ℂ W {s : ℂ | a < s.re})
    (heq : ∀ s : ℂ, max a b < s.re → L s * M s = W s) :
    Set.EqOn (fun s => L s * M s) W {s : ℂ | a < s.re} := by
  let z : ℂ := (max a b + 1 : ℝ)
  have hz : a < z.re := by dsimp [z]; linarith [le_max_left a b]
  have hz' : max a b < z.re := by dsimp [z]; simp
  have hev : (fun s => L s * M s) =ᶠ[𝓝 z] W := by
    filter_upwards [(Complex.isOpen_re_gt (max a b)).mem_nhds hz'] with s hs
    exact heq s hs
  exact (hL.mul hM).eqOn_of_preconnected_of_eventuallyEq hW
    (convex_halfSpace_re_gt a).isPreconnected hz hev

end SevenEighths.Continuation

end

end OAI
end

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.MobiusEulerCorrection
namespace OAI

noncomputable section

namespace SmoothMobiusCorrection

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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical

section
open ActualEisensteinCubic
open IdealMobiusDivisorSum hiding O
open UniqueFactorizationMonoid
open CanonicalRowCompletion (primeValueHom primeValueHom_prime)

theorem primeProduct_ne_zero (s : Finset PrimeIdeal) : primeProduct s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => P.property.ne_zero)

theorem factors_primeProduct (s : Finset PrimeIdeal) :
    normalizedFactors (primeProduct s) = s.val.map Subtype.val := by
  have h := normalizedFactors_prod_of_prime
    (m := s.val.map (fun P : PrimeIdeal => P.val)) (by
      intro P hP
      obtain ⟨Q,hQ,rfl⟩ := Multiset.mem_map.mp hP
      exact Q.property)
  simpa only [primeProduct, Finset.prod_eq_multiset_prod] using h

theorem primeSet_primeProduct (s : Finset PrimeIdeal) : primeSet (primeProduct s) = s := by
  ext P
  rw [mem_primeSet]
  simp only [primeSupport, factors_primeProduct, Multiset.mem_toFinset,
    Multiset.mem_map, Finset.mem_val]
  constructor
  · rintro ⟨Q,hQ,he⟩
    have : Q=P := Subtype.ext he
    simpa [this] using hQ
  · intro h
    exact ⟨P,h,rfl⟩

theorem primeProduct_injective : Function.Injective primeProduct := by
  intro s t h
  simpa only [primeSet_primeProduct] using congrArg primeSet h

theorem primeProduct_squarefree (s : Finset PrimeIdeal) : Squarefree (primeProduct s) := by
  rw [squarefree_iff_nodup_normalizedFactors (primeProduct_ne_zero s),factors_primeProduct]
  exact s.nodup.map Subtype.val_injective

theorem primeProduct_primeSet (I : Ideal ActualEisensteinCubic.O) (hI : Squarefree I) :
    primeProduct (primeSet I) = I := by
  unfold primeProduct primeSet
  rw [Finset.prod_image]
  · change (∏ P ∈ (primeSupport I).attach, (fun Q : Ideal ActualEisensteinCubic.O => Q) P.val) = I
    exact (Finset.prod_attach (primeSupport I) (fun Q : Ideal ActualEisensteinCubic.O => Q)).trans
      (squarefree_support_product_self hI)
  · intro P hP Q hQ he
    exact Subtype.ext (congrArg (fun R : PrimeIdeal => R.val) he)

theorem mobiusPrimeCoeff_nonsquarefree (w : Ideal ActualEisensteinCubic.O → ℂ) (I : Ideal ActualEisensteinCubic.O)
    (hI : ¬Squarefree I) : mobiusPrimeCoeff w I=0 := by
  simp [mobiusPrimeCoeff,moebius_of_not_squarefree hI]

theorem mobiusPrimeCoeff_primeProduct (w : Ideal ActualEisensteinCubic.O → ℂ) (s : Finset PrimeIdeal) :
    mobiusPrimeCoeff w (primeProduct s) = ∏ P ∈ s, -w P.val := by
  have hm : (moebius (primeProduct s) : ℂ)=(-1:ℂ)^s.card := by
    rw [(primeProduct_squarefree s).moebius_eq,factors_eq_normalizedFactors,
      factors_primeProduct]
    simp
  rw [mobiusPrimeCoeff,hm]
  simp only [primeProduct,map_prod,primeValueHom_prime _ _ (Subtype.property _)]
  rw [Finset.prod_neg]

theorem mobiusPrimeCoeff_tsum (w : Ideal ActualEisensteinCubic.O → ℂ) :
    (∑' I : Ideal ActualEisensteinCubic.O, mobiusPrimeCoeff w I) =
      ∑' s : Finset PrimeIdeal, ∏ P ∈ s, -w P.val := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun s => primeProduct s.val)
  · exact primeProduct_injective.comp Subtype.val_injective
  · intro I hI
    have hs : Squarefree I := by
      by_contra hs
      exact hI (mobiusPrimeCoeff_nonsquarefree w I hs)
    have hp : (∏ P ∈ primeSet I, -w P.val) ≠ 0 := by
      rw [←mobiusPrimeCoeff_primeProduct,primeProduct_primeSet I hs]
      exact hI
    exact ⟨⟨primeSet I,hp⟩,primeProduct_primeSet I hs⟩
  · intro s
    exact mobiusPrimeCoeff_primeProduct w s.val

theorem mobiusPrimeCoeff_euler (w : Ideal ActualEisensteinCubic.O → ℂ)
    (hw : Summable (fun P : PrimeIdeal => ‖w P.val‖)) :
    (∑' I : Ideal ActualEisensteinCubic.O, mobiusPrimeCoeff w I) =
      ∏' P : PrimeIdeal, (1-w P.val) := by
  rw [mobiusPrimeCoeff_tsum]
  have hs : Summable (fun P : PrimeIdeal => ‖-w P.val‖) := by simpa using hw
  simpa only [sub_eq_add_neg] using
    (tprod_one_add (summable_finsetProd_of_summable_norm hs)).symm

end

section
open ActualEisensteinCubic
open Filter

lemma prime_norm_pos (P : PrimeIdeal) : (0 : ℝ) < Ideal.absNorm P.val := by
  have h := prime_norm_two_le P
  exact_mod_cast (by omega : 0 < Ideal.absNorm P.val)

lemma norm_primeNormPower (P : PrimeIdeal) (s : ℂ) :
    ‖primeNormPower P s‖=(Ideal.absNorm P.val : ℝ)^(-s.re) := by
  exact Complex.norm_cpow_eq_rpow_re_of_pos (prime_norm_pos P) (-s)

lemma one_sub_ne_zero {x : ℂ} (hx : ‖x‖<1) : 1-x≠0 := by
  intro h
  have he : x=1 := (sub_eq_zero.mp h).symm
  simp [he] at hx

end

open ActualEisensteinCubic

open scoped BigOperators Classical
open ActualEisensteinCubic
open ShortDraftHeckeBridge hiding O

end SmoothMobiusCorrection

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SourceMellinInversion
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CompletedGauss

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

section
open ActualEisensteinCubic CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma nonzeroIdeal_norm_rpow_summable (σ : ℝ) (hσ : 1<σ) :
    Summable (fun I : NonzeroIdeal=>(Ideal.absNorm I.1:ℝ)^(-σ)) := by
  have h := (fullIdealWeight_summable_norm (σ:ℂ) (by simpa using hσ)).subtype (fun I=>I≠0)
  apply h.congr
  intro I
  change ‖fullIdealWeight (σ:ℂ) I.1‖=(Ideal.absNorm I.1:ℝ)^(-σ)
  rw [fullIdealWeight,if_neg I.2]
  simpa only [Complex.neg_re,Complex.ofReal_re,Complex.ofReal_natCast] using
    (Complex.norm_cpow_eq_rpow_re_of_pos (nonzeroIdeal_norm_pos I) (-(σ:ℂ)))

end

open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

end CompletedGauss

open scoped BigOperators Classical
open Finset AddChar MulChar EisensteinEmbedding

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.EulerFactors
namespace OAI

namespace SevenEighths.EulerFactors

noncomputable section

theorem norm_term_lt_one {N : ℝ} (hN : 1 < N) {a s : ℂ}
    (ha : ‖a‖ ≤ 1) (hs : 0 < s.re) : ‖a * (N : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < N),
    Complex.neg_re]
  calc
    ‖a‖ * N ^ (-s.re) ≤ 1 * N ^ (-s.re) :=
      mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg (by linarith) _)
    _ < 1 := by simpa using Real.rpow_lt_one_of_one_lt_of_neg hN (neg_neg_of_pos hs)

theorem factor_ne_zero {N : ℝ} (hN : 1 < N) {a s : ℂ}
    (ha : ‖a‖ ≤ 1) (hs : 0 < s.re) : factor N a s ≠ 0 := by
  intro h
  have heq : a * (N : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hlt := norm_term_lt_one hN ha hs
  rw [heq, norm_one] at hlt
  exact (lt_irrefl _ hlt)

theorem differentiable_factor {N : ℝ} (hN : 0 < N) (a : ℂ) :
    Differentiable ℂ (factor N a) := by
  exact (differentiable_const (1 : ℂ)).sub ((differentiable_const a).mul
    (differentiable_id.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hN.ne'))))

theorem deletedProduct_ne_zero {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 1 < N p) (ha : ∀ p ∈ S, ‖a p‖ ≤ 1)
    {s : ℂ} (hs : 0 < s.re) : deletedProduct S N a s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact factor_ne_zero (hN p hp) (ha p hp) hs

theorem differentiable_deletedProduct {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 0 < N p) :
    Differentiable ℂ (deletedProduct S N a) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    change Differentiable ℂ (fun _ : ℂ => (1 : ℂ))
    exact differentiable_const _
  | @insert p S hp ih =>
    have hpN := hN p (Finset.mem_insert_self p S)
    have hSN : ∀ q ∈ S, 0 < N q := fun q hq => hN q (Finset.mem_insert_of_mem hq)
    have heq : deletedProduct (insert p S) N a =
        fun s => factor (N p) (a p) s * deletedProduct S N a s := by
      funext s
      simp only [deletedProduct, Finset.prod_insert hp]
    rw [heq]
    exact (differentiable_factor hpN (a p)).mul (ih hSN)

end

end SevenEighths.EulerFactors

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Theta
namespace OAI

noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators
namespace SevenEighths.HeckeTheta
open EisensteinTheta

theorem regularizedCompleted_differentiableAt {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (regularizedCompleted w) s := by
  exact (((differentiableAt_id.sub_const 1).mul
    (((pair w).differentiable_Λ₀ s).sub
      ((differentiableAt_id.inv hs₀).mul_const (pair w).f₀))).add_const (pair w).g₀)

theorem regularizedCompleted_eq {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    regularizedCompleted w s = (s - 1) * completed w s := by
  unfold regularizedCompleted completed WeakFEPair.Λ
  simp only [pair_k, Complex.ofReal_one, show (pair w).ε = 1 from rfl,
    smul_eq_mul, one_div]
  have hsub : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs₁.symm
  field_simp
  ring

theorem regularizedLatticeL_differentiableAt {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (regularizedLatticeL w) s := by
  exact (((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt).mul
      (Complex.differentiable_one_div_Gamma s)).mul
        (regularizedCompleted_differentiableAt w hs₀)

theorem regularizedLatticeL_eq {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    regularizedLatticeL w s = (s - 1) * latticeL w s := by
  unfold regularizedLatticeL latticeL
  rw [regularizedCompleted_eq w hs₀ hs₁]
  ring

end SevenEighths.HeckeTheta

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.IdealCharacter
namespace OAI

namespace SevenEighths.IdealCharacter

open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open SevenEighths.ConductorPresentation
open Submodule.IsPrincipal
open scoped Classical

noncomputable section

variable {A : Type*} [CommRing A]

section Principal

variable [IsDomain A] [IsPrincipalIdealRing A]

theorem ofResidue_finite_deletion (M K : Ideal A)
    (χ : MulChar (A ⧸ M) ℂ) (φ : MulChar (A ⧸ K) ℂ)
    (hχ : UnitInvariant M χ) (hφ : UnitInvariant K φ)
    (hmask : ∀ a : A, χ (Ideal.Quotient.mk M a) =
      if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0)
    (I : Ideal A) :
    ofResidue M χ hχ I =
      ofResidue M 1 (one_unitInvariant M) I * ofResidue K φ hφ I := by
  rw [ofResidue_source_mask M K χ φ hχ hφ hmask, ofResidue_one]
  by_cases hI : I = ⊥
  · simp only [hI, ofResidue_bot, ite_true, ite_self, mul_zero]
  · simp only [hI, ite_false]
    split_ifs <;> simp only [one_mul, zero_mul]

section Primitive

variable [Infinite A] [Module.Free ℤ A] [Module.Finite ℤ A]

theorem exists_primitive_associate (M : Ideal A) [Finite (A ⧸ M)]
    (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ) (hφ : UnitInvariant K φ),
      M ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ M.absNorm ∧
      (∀ I : Ideal A, ofResidue M χ hχ I =
        if IsCoprime I M then ofResidue K φ hφ I else 0) ∧
      ∀ I : Ideal A, ofResidue M χ hχ I =
        ofResidue M 1 (one_unitInvariant M) I * ofResidue K φ hφ I := by
  obtain ⟨K, φ, hMK, hK, hprimitive, hnorm, hmask⟩ := exists_primitive_presentation M χ
  have hφ : UnitInvariant K φ := by
    intro u
    have h := hmask (u : A)
    simpa only [hχ u, u.isUnit.map (Ideal.Quotient.mk M), ite_true] using h.symm
  exact ⟨K, φ, hφ, hMK, hK, hprimitive, hnorm,
    ofResidue_source_mask M K χ φ hχ hφ hmask,
    ofResidue_finite_deletion M K χ φ hχ hφ hmask⟩

end Primitive

end Principal

end

end SevenEighths.IdealCharacter

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.IdealOperations
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeFamily

theorem exists_primitive_character (χ : Character) :
    ∃ ψ : Character,
      χ.modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ χ.modulus.absNorm ∧
      ∀ I : Ideal O, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff ψ I else 0 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  obtain ⟨M, φ, hφ, hM, hM₀, hprim, hnorm, hmask, _⟩ :=
    IdealCharacter.exists_primitive_associate χ.modulus χ.residue χ.unit_trivial
  exact ⟨Character.ofResidue M hM₀ φ hφ, hM, hprim, hnorm, hmask⟩

end SevenEighths.HeckeFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.IdealEuler
namespace OAI

namespace SevenEighths.IdealEuler

open ActualEisensteinCubic UniqueFactorizationMonoid
open CompletedGauss (MulFiber mulFiber_moebius_sum)
open SmoothMobiusCorrection (PrimeIdeal)
open scoped BigOperators Classical

noncomputable section

theorem inverseSeries_eq_inv (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : inverseSeries a s = (series a s)⁻¹ := by
  calc
    _ = (inverseSeries a s * series a s) * (series a s)⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ (series_ne_zero a ha s hs), mul_one]
    _ = _ := by rw [inverseSeries_mul_series a ha s hs, one_mul]

theorem prime_summable_norm (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Summable (fun P : PrimeIdeal => ‖weighted a s P.val‖) :=
  (weighted_summable_norm a ha s hs).comp_injective Subtype.val_injective

theorem prime_norm_lt_one (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 0 < s.re) (P : PrimeIdeal) : ‖weighted a s P.val‖ < 1 := by
  change ‖a P.val * CubicEisenstein.fullIdealWeight s P.val‖ < 1
  simp only [CubicEisenstein.fullIdealWeight, P.property.ne_zero, ite_false, norm_mul]
  change ‖a P.val‖ * ‖SmoothMobiusCorrection.primeNormPower P s‖ < 1
  rw [SmoothMobiusCorrection.norm_primeNormPower]
  apply (mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _) (ha P.val)).trans_lt
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by have h := SmoothMobiusCorrection.prime_norm_two_le P
        exact_mod_cast (by omega : 1 < Ideal.absNorm P.val)) (by simpa using neg_neg_of_pos hs)

theorem local_factor_ne_zero (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 0 < s.re) (P : PrimeIdeal) : 1 - weighted a s P.val ≠ 0 :=
  SmoothMobiusCorrection.one_sub_ne_zero (prime_norm_lt_one a ha s hs P)

theorem inverseSeries_euler (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    inverseSeries a s = ∏' P : PrimeIdeal, (1 - weighted a s P.val) := by
  have h := SmoothMobiusCorrection.mobiusPrimeCoeff_euler (weighted a s)
    (prime_summable_norm a ha s hs)
  simpa only [SmoothMobiusCorrection.mobiusPrimeCoeff, primeValueHom_eq, inverseSeries] using h

theorem euler_hasProd (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun P : PrimeIdeal => (1 - weighted a s P.val)⁻¹) (series a s) := by
  have hm : Multipliable (fun P : PrimeIdeal => 1 - weighted a s P.val) := by
    simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable
      (show Summable (fun P : PrimeIdeal => ‖-weighted a s P.val‖) by
        simpa only [norm_neg] using prime_summable_norm a ha s hs)
  have heq : (∏' P : PrimeIdeal, (1 - weighted a s P.val)) = (series a s)⁻¹ :=
    (inverseSeries_euler a ha s hs).symm.trans (inverseSeries_eq_inv a ha s hs)
  have hne : (∏' P : PrimeIdeal, (1 - weighted a s P.val)) ≠ 0 := by
    rw [heq]
    exact inv_ne_zero (series_ne_zero a ha s hs)
  simpa only [heq, inv_inv] using hm.hasProd.inv₀ hne

theorem series_euler (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    series a s = ∏' P : PrimeIdeal, (1 - weighted a s P.val)⁻¹ :=
  (euler_hasProd a ha s hs).tprod_eq.symm

theorem deletePrimes_prime (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ) (P : PrimeIdeal) :
    deletePrimes S a P.val = if P ∈ S then 0 else a P.val := by
  have hmem : P.val ∈ S.image Subtype.val ↔ P ∈ S := by
    constructor
    · intro hP
      obtain ⟨Q, hQ, hQP⟩ := Finset.mem_image.mp hP
      exact (Subtype.ext hQP : Q = P) ▸ hQ
    · intro hP
      exact Finset.mem_image.mpr ⟨P, hP, rfl⟩
  change CanonicalRowCompletion.primeValueHom _ P.val = _
  rw [CanonicalRowCompletion.primeValueHom_prime _ _ P.property]
  simp only [hmem]

theorem deletePrimes_norm_le_one (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) : ∀ I, ‖deletePrimes S a I‖ ≤ 1 := by
  apply CanonicalRowCompletion.primeValueHom_norm_le_one
  intro I
  split_ifs
  · simp only [norm_zero, zero_le_one]
  · exact ha I

theorem deletePrimes_apply (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ) (I : Ideal O) :
    deletePrimes S a I = if ∀ P ∈ S, ¬P.val ∣ I then a I else 0 := by
  by_cases ho : ∀ P ∈ S, ¬P.val ∣ I
  · rw [if_pos ho]
    by_cases hI : I = 0
    · subst I
      rw [map_zero, map_zero]
    · change (if I = 0 then 0 else
        ((normalizedFactors I).map (fun J => if J ∈ S.image Subtype.val then 0 else a J)).prod) = a I
      simp only [hI, ite_false]
      have hmap : (normalizedFactors I).map (fun J => if J ∈ S.image Subtype.val then 0 else a J) =
          (normalizedFactors I).map a := by
        apply Multiset.map_congr rfl
        intro J hJ
        have hnot : J ∉ S.image Subtype.val := by
          intro hmem
          obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hmem
          exact ho P hP (dvd_of_mem_normalizedFactors hJ)
        simp only [hnot, ite_false]
      rw [hmap, ← map_multiset_prod, prod_normalizedFactors_eq hI, normalize_eq]
  · simp only [ho, ite_false]
    push Not at ho
    obtain ⟨P, hPS, J, hJ⟩ := ho
    rw [hJ, map_mul, deletePrimes_prime]
    simp only [hPS, ite_true, zero_mul]

theorem deletePrimes_primeSet_apply (M : Ideal O) (hM : M ≠ 0)
    (a : Ideal O →*₀ ℂ) (I : Ideal O) :
    deletePrimes (SmoothMobiusCorrection.primeSet M) a I =
      if IsCoprime I M then a I else 0 := by
  by_cases hI : I = 0
  · subst I
    rw [map_zero, map_zero]
    exact (ite_self _).symm
  have heq : (∀ P ∈ SmoothMobiusCorrection.primeSet M, ¬P.val ∣ I) ↔ IsCoprime I M := by
    rw [← IdealCoprimeSieveOperator.primeSupport_disjoint_iff hI hM]
    constructor
    · intro h
      apply Finset.disjoint_left.mpr
      intro P hPI hPM
      have hp : Prime P := IdealMobiusDivisorSum.support_prime hPM
      exact h ⟨P, hp⟩ (SmoothMobiusCorrection.mem_primeSet M ⟨P, hp⟩ |>.mpr hPM)
        (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hPI))
    · intro h P hPM hPI
      exact Finset.disjoint_left.mp h
        (Multiset.mem_toFinset.mpr ((mem_normalizedFactors_iff hI).mpr ⟨P.property, hPI⟩))
        ((SmoothMobiusCorrection.mem_primeSet M P).mp hPM)
  simpa only [heq] using deletePrimes_apply (SmoothMobiusCorrection.primeSet M) a I

theorem series_deletePrimes (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    series (deletePrimes S a) s =
      series a s * ∏ P ∈ S, (1 - weighted a s P.val) := by
  have hlocal (P : PrimeIdeal) :
      (1 - weighted (deletePrimes S a) s P.val)⁻¹ =
        (1 - weighted a s P.val)⁻¹ * (if P ∈ S then 1 - weighted a s P.val else 1) := by
    change (1 - deletePrimes S a P.val * normWeight s P.val)⁻¹ = _
    rw [deletePrimes_prime]
    by_cases hP : P ∈ S
    · simp only [hP, ite_true, zero_mul, sub_zero, inv_one]
      exact (inv_mul_cancel₀ (local_factor_ne_zero a ha s (by linarith) P)).symm
    · simp only [hP, ite_false, mul_one]
      rfl
  have hfinite : Multipliable (fun P : PrimeIdeal => if P ∈ S then 1 - weighted a s P.val else 1) := by
    apply multipliable_of_hasFiniteMulSupport
    apply S.finite_toSet.subset
    intro P hP
    by_contra hPS
    change P ∉ S at hPS
    exact hP (by simp only [hPS, ite_false])
  rw [series_euler _ (deletePrimes_norm_le_one S a ha) s hs,
    series_euler a ha s hs]
  simp_rw [hlocal]
  rw [(euler_hasProd a ha s hs).multipliable.tprod_mul hfinite]
  congr 1
  rw [tprod_eq_prod (s := S) (fun P hP => by simp only [hP, ite_false])]
  exact Finset.prod_congr rfl (fun P hP => by simp only [hP, ite_true])

theorem series_of_coprime_mask (M : Ideal O) (hM : M ≠ 0)
    (a b : Ideal O →*₀ ℂ) (hb : ∀ I, ‖b I‖ ≤ 1)
    (hmask : ∀ I, a I = if IsCoprime I M then b I else 0)
    (s : ℂ) (hs : 1 < s.re) :
    series a s = series b s *
      ∏ P ∈ SmoothMobiusCorrection.primeSet M, (1 - weighted b s P.val) := by
  have heq : a = deletePrimes (SmoothMobiusCorrection.primeSet M) b := by
    ext I
    rw [deletePrimes_primeSet_apply M hM, hmask]
  rw [heq]
  exact series_deletePrimes _ b hb s hs

end

end SevenEighths.IdealEuler

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Reciprocal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeReciprocal
open HeckeFamily HeckeCharacterAnalytic HeckeCoordinates

theorem regularizedL_eq (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    regularizedL χ s = (s - 1) * LFunction χ s := by
  unfold regularizedL LFunction continuedLattice
  rw [HeckeTheta.regularizedLatticeL_eq _ h0 h1]
  ring

theorem regularizedL_differentiableAt (χ : Character) {s : ℂ} (h0 : s ≠ 0) :
    DifferentiableAt ℂ (regularizedL χ) s :=
  (HeckeTheta.regularizedLatticeL_differentiableAt _ h0).div_const 6

end SevenEighths.HeckeReciprocal

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeFiniteDeletion
open HeckeFamily HeckeReciprocal

theorem factors_eq (M : Ideal O) (ψ : Character) (s : ℂ) :
    factors M ψ s = ∏ P ∈ SmoothMobiusCorrection.primeSet M,
      (1 - IdealEuler.weighted (idealCoeff ψ) s P.val) := by
  apply Finset.prod_congr rfl
  intro P _
  simp only [EulerFactors.factor, IdealEuler.weighted, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, IdealEuler.normWeight, CubicEisenstein.fullIdealWeight,
    P.property.ne_zero, ite_false, Complex.ofReal_natCast]

theorem factors_differentiable (M : Ideal O) (ψ : Character) :
    Differentiable ℂ (factors M ψ) := by
  apply EulerFactors.differentiable_deletedProduct
  intro P _
  have h := SmoothMobiusCorrection.prime_norm_two_le P
  exact_mod_cast (by omega : 0 < Ideal.absNorm P.val)

theorem factors_ne_zero (M : Ideal O) (ψ : Character) {s : ℂ} (hs : 0 < s.re) :
    factors M ψ s ≠ 0 := by
  apply EulerFactors.deletedProduct_ne_zero _ _ _ _ _ hs
  · intro P _
    have h := SmoothMobiusCorrection.prime_norm_two_le P
    exact_mod_cast (by omega : 1 < Ideal.absNorm P.val)
  · intro P _
    exact idealCoeff_norm_le_one ψ P.val

theorem LFunction_eq_of_mask_right (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = LFunction ψ s * factors χ.modulus ψ s := by
  rw [LFunction_eq_series χ hs, LFunction_eq_series ψ hs, factors_eq]
  exact IdealEuler.series_of_coprime_mask χ.modulus χ.modulus_ne_bot
    _ _ (idealCoeff_norm_le_one ψ) hmask s hs

theorem regularizedL_analytic (χ : Character) :
    AnalyticOnNhd ℂ (regularizedL χ) {s : ℂ | 0 < s.re} := by
  apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
  intro s hs
  exact (regularizedL_differentiableAt χ (by intro h; simp [h] at hs)).differentiableWithinAt

theorem regularizedL_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) :
    regularizedL χ s = regularizedL ψ s * factors χ.modulus ψ s := by
  have hf : AnalyticOnNhd ℂ (factors χ.modulus ψ) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
    exact (factors_differentiable _ _).differentiableOn
  apply Eq.symm
  apply Continuation.product_identity_on_halfPlane 0 1
    (regularizedL ψ) (factors χ.modulus ψ) (regularizedL χ)
    (regularizedL_analytic ψ) hf (regularizedL_analytic χ) _ hs
  intro z hz
  have hz' : 1 < z.re := by simpa using hz
  have h0 : z ≠ 0 := by intro h; norm_num [h] at hz'
  have h1 : z ≠ 1 := by intro h; norm_num [h] at hz'
  rw [regularizedL_eq χ h0 h1, regularizedL_eq ψ h0 h1,
    LFunction_eq_of_mask_right χ ψ hmask hz']
  ring

theorem regularizedL_one_ne_zero_iff (χ : Character) :
    regularizedL χ 1 ≠ 0 ↔ χ.residue = 1 := by
  constructor
  · intro h
    by_contra hχ
    rw [regularizedL_at_one,
      HeckeTheta.pair_g₀_eq_zero _ (HeckeCharacterAnalytic.coefficients_sum_eq_zero χ hχ),
      mul_zero, zero_div] at h
    exact h rfl
  · exact regularizedL_ne_zero_at_one χ

theorem principal_iff_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0) :
    χ.residue = 1 ↔ ψ.residue = 1 := by
  rw [← regularizedL_one_ne_zero_iff χ, ← regularizedL_one_ne_zero_iff ψ,
    regularizedL_eq_of_mask χ ψ hmask (by norm_num : 0 < (1 : ℂ).re),
    mul_ne_zero_iff, and_iff_left (factors_ne_zero χ.modulus ψ (by norm_num))]

end SevenEighths.HeckeFiniteDeletion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.TraceCharacter
namespace OAI

noncomputable section

open scoped BigOperators SchwartzMap

namespace SevenEighths.TraceCharacter

open ActualEisensteinCubic EisensteinEmbedding ConcreteTraceCRT
open EisensteinSchwartzPoisson FiniteFourier

variable (c : O) [NeZero c]

attribute [local instance] OAI.SevenEighths.TraceCharacter.residueFinite
attribute [local instance] OAI.SevenEighths.TraceCharacter.residueFintype
theorem primitive_radial_paper_poisson (W : 𝓢(ℝ, ℂ)) (scale : ℝ)
    (hscale : 0 < scale) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * gaussScalar c χ / (Ideal.absNorm (Ideal.span {c}) : ℂ)) *
        ∑' h : O, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) *
          paperRadialFourier W
            (scale * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (Ideal.span {c}) : ℝ)) := by
  have hp := actual_radial_paper_poisson_trace W scale hscale c (NeZero.ne c) χ
  change _ = (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
    (∑ x : O ⧸ Ideal.span {c}, χ x *
      traceCharacter c (NeZero.ne c) (Ideal.Quotient.mk (Ideal.span {c}) h * x)) *
        paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  simp_rw [transform_eq c χ hχ, eisEmbedding_norm_sq_eq_absNorm_span c] at hp
  rw [hp, ← tsum_mul_left]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro h
  ring

theorem primitive_radial_paper_poisson_normalized (W : 𝓢(ℝ, ℂ)) (scale : ℝ)
    (hscale : 0 < scale) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * normalizedGauss c χ / (‖eisEmbedding c‖ : ℂ)) *
        ∑' h : O, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  have hp := primitive_radial_paper_poisson c W scale hscale χ hχ
  rw [← eisEmbedding_norm_sq_eq_absNorm_span c] at hp
  have hnorm : (Ideal.absNorm (Ideal.span {c}) : ℂ) = (‖eisEmbedding c‖ : ℂ) ^ 2 := by
    exact_mod_cast (eisEmbedding_norm_sq_eq_absNorm_span c).symm
  rw [hnorm] at hp
  rw [hp]
  congr 1
  rw [normalizedGauss]
  have hn : (‖eisEmbedding c‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c)))
  field_simp

end SevenEighths.TraceCharacter

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ComparisonReflection
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentComparisonReflection
open HeckeFamily HeckePrimitive ActualEisensteinCubic ConcreteTraceCRT
open EisensteinSchwartzPoisson ConcretePrimeRowBridge GaussGeneratorTransport
local notation "O" => HeckeFamily.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma residue_nontrivial (c : O) (χ : MulChar (O⧸Ideal.span {c}) ℂ) (hχ : χ≠1) :
    Nontrivial (O⧸Ideal.span {c}) := by
  by_contra h
  have : Subsingleton (O⧸Ideal.span {c}) := not_nontrivial_iff_subsingleton.mp h
  apply hχ
  ext x
  have hx : x=1 := Subsingleton.elim _ _
  simp [hx]

lemma residue_zero (c : O) [NeZero c] (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀u:Oˣ,χ (Ideal.Quotient.mk (Ideal.span {c}) u.val)=1) (hχ : χ≠1) :
    elementCoeff (character c χ hu) 0=0 := by
  let := residue_nontrivial c χ hχ
  change χ (Ideal.Quotient.mk (Ideal.span {c}) 0)=0
  rw [map_zero,χ.map_zero]

theorem radial_ideal_reindex (η : Character) (W : ℝ→ℂ) (X : ℝ)
    (hzero : elementCoeff η 0=0)
    (hs : Summable (fun z : O => elementCoeff η z*W (‖eisEmbedding z‖^2/X))) :
    (∑' z : O,elementCoeff η z*W (‖eisEmbedding z‖^2/X))=
      6*∑' I : NI,idealCoeff η I.val*W ((I.val.absNorm:ℝ)/X) := by
  have h := UnrestrictedIdealReindex.tsum_unit_invariant_of_zero
    (fun z : O => elementCoeff η z*W (‖eisEmbedding z‖^2/X)) hs
    (by rw [hzero,zero_mul])
    (fun u z => by rw [elementCoeff_unit_mul,norm_eisEmbedding_unit_mul])
  rw [h]
  congr 1
  apply tsum_congr
  intro I
  rw [eisEmbedding_norm_sq_eq_absNorm_span,span_idealGenerator]
  congr 1
  exact (IdealCharacter.ofResidue_of_generator η.modulus η.residue η.unit_trivial
    I.property (span_idealGenerator I.val)).symm

lemma bounded_radial_summable (η : Character) (W : ℝ→ℂ) (X : ℝ)
    (hs : Summable (fun z : O => ‖W (‖eisEmbedding z‖^2/X)‖)) :
    Summable (fun z : O => elementCoeff η z*W (‖eisEmbedding z‖^2/X)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ hs
  intro z
  rw [norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  let : Finite (O⧸η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (O⧸η.modulus) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one η.residue _

theorem primitive_plain_reflection (c : O) [NeZero c]
    (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀u:Oˣ,χ (Ideal.Quotient.mk (Ideal.span {c}) u.val)=1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ≠1)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0<X) :
    (∑' I : NI,idealCoeff (character c χ hu) I.val*W ((I.val.absNorm:ℝ)/X))=
      ((X:ℂ)*TraceCharacter.normalizedGauss c χ/(‖eisEmbedding c‖:ℂ))*
      ∑' I : NI,idealCoeff (character c χ⁻¹ (inverse_unit_trivial c χ hu)) I.val*
        paperRadialFourier W ((I.val.absNorm:ℝ)/(‖eisEmbedding c‖^2/X)) := by
  have hc : 0<‖eisEmbedding c‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))
  have hQ : 0<‖eisEmbedding c‖^2 := sq_pos_of_pos hc
  have hχi : χ⁻¹≠1 := inv_ne_one.mpr hχ
  have hs : Summable (fun z : O => ‖W (‖eisEmbedding z‖^2/X)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest W X hX)
  have hd : Summable (fun z : O => ‖paperRadialFourier W
      (‖eisEmbedding z‖^2/(‖eisEmbedding c‖^2/X))‖) := by
    convert (preTransparency := .instances) paperRadialFourier_lattice_summable_norm W (X/‖eisEmbedding c‖^2) (div_pos hX hQ) using 1
    funext z
    congr 2
    field_simp
  have he := TraceCharacter.primitive_radial_paper_poisson_normalized c W X hX χ hp
  have he' : (∑' z : O,elementCoeff (character c χ hu) z*W (‖eisEmbedding z‖^2/X))=
      ((X:ℂ)*TraceCharacter.normalizedGauss c χ/(‖eisEmbedding c‖:ℂ))*
      ∑' z : O,elementCoeff (character c χ⁻¹ (inverse_unit_trivial c χ hu)) z*
        paperRadialFourier W (‖eisEmbedding z‖^2/(‖eisEmbedding c‖^2/X)) := by
    change (∑' z : O,χ (Ideal.Quotient.mk (Ideal.span {c}) z)*W (‖eisEmbedding z‖^2/X))=_
    rw [he]
    congr 1
    apply tsum_congr
    intro z
    congr 2
    field_simp
  rw [radial_ideal_reindex _ W X (residue_zero c χ hu hχ) (bounded_radial_summable _ W X hs),
    radial_ideal_reindex _ (paperRadialFourier W) _ (residue_zero c χ⁻¹ _ hχi)
      (bounded_radial_summable _ (paperRadialFourier W) _ hd)] at he'
  linear_combination he'/6

lemma inverse_half_power (X : ℝ) (hX : 0≤X) :
    (X:ℂ)^(-(1/2:ℂ))=(Real.sqrt X:ℂ)⁻¹ := by
  rw [Complex.cpow_neg]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using (Complex.ofReal_cpow hX (1/2)).symm

lemma polynomial_plain (η : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial η false W X 0 0=
      (Real.sqrt X:ℂ)⁻¹*∑' I : NI,idealCoeff η I.val*W ((I.val.absNorm:ℝ)/X) := by
  simp only [HeckeDyadic.polynomial,HeckeDyadic.summand,HeckeDyadic.coefficient,
    Bool.false_eq_true,ite_false,HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,
    sub_zero,neg_zero,Complex.cpow_zero,mul_one,HeckeDyadic.norm]
  rw [inverse_half_power X hX.le]

theorem primitive_normalized_reflection (c : O) [NeZero c]
    (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀u:Oˣ,χ (Ideal.Quotient.mk (Ideal.span {c}) u.val)=1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ≠1)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial (character c χ hu) false W X 0 0=
      TraceCharacter.normalizedGauss c χ*
        HeckeDyadic.polynomial (character c χ⁻¹ (inverse_unit_trivial c χ hu)) false
          (paperRadialFourier W) (‖eisEmbedding c‖^2/X) 0 0 := by
  have hc : 0<‖eisEmbedding c‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))
  have hY : 0<‖eisEmbedding c‖^2/X := div_pos (sq_pos_of_pos hc) hX
  rw [polynomial_plain _ _ _ hX,primitive_plain_reflection c χ hu hp hχ W X hX,
    polynomial_plain _ _ _ hY]
  have hs : Real.sqrt (‖eisEmbedding c‖^2/X)=‖eisEmbedding c‖/Real.sqrt X := by
    rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq hc.le]
  have hx : (Real.sqrt X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  have hcn : (‖eisEmbedding c‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hsq : (Real.sqrt X:ℂ)^2=(X:ℂ) := by exact_mod_cast Real.sq_sqrt hX.le
  have hfac : (Real.sqrt X:ℂ)⁻¹*((X:ℂ)*TraceCharacter.normalizedGauss c χ/(‖eisEmbedding c‖:ℂ))=
      TraceCharacter.normalizedGauss c χ*(Real.sqrt (‖eisEmbedding c‖^2/X):ℂ)⁻¹ := by
    rw [hs,Complex.ofReal_div]
    field_simp
    rw [hsq]
  rw [←mul_assoc,hfac,mul_assoc]

end SevenEighths.CenteredMomentComparisonReflection

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalPrimitive
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentNaturalPrimitive
open HeckeFamily IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

lemma redundantSet_subset (M C : Ideal O) : redundantSet M C⊆primeSupport M :=
  Finset.sdiff_subset

lemma redundantIdeal_squarefree (M C : Ideal O) : Squarefree (redundantIdeal M C) :=
  squarefree_support_product (redundantSet_subset M C)

lemma redundantIdeal_ne_zero (M C : Ideal O) : redundantIdeal M C≠0 :=
  support_product_ne_zero (redundantSet_subset M C)

lemma redundantIdeal_support (M C : Ideal O) : primeSupport (redundantIdeal M C)=redundantSet M C := by
  unfold primeSupport redundantIdeal
  rw [factors_support_product (redundantSet_subset M C)]
  exact Finset.val_toFinset _

lemma redundantIdeal_coprime (M C : Ideal O) (hC : C≠0) : IsCoprime (redundantIdeal M C) C := by
  apply (IdealCoprimeSieveOperator.primeSupport_disjoint_iff (redundantIdeal_ne_zero M C) hC).mp
  rw [redundantIdeal_support]
  exact Finset.disjoint_left.mpr (fun P hp hc=>(Finset.mem_sdiff.mp hp).2 hc)

lemma primitive_redundant_dvd (M C : Ideal O) (hM : M≠0) (hC : C≠0) (hCM : C∣M) :
    C*redundantIdeal M C∣M := by
  exact (redundantIdeal_coprime M C hC).symm.mul_dvd hCM
    (support_product_dvd hM (redundantSet_subset M C))

lemma primitive_redundant_norm (M C : Ideal O) (hM : M≠0) (hC : C≠0) (hCM : C∣M) :
    C.absNorm*(redundantIdeal M C).absNorm≤M.absNorm := by
  have h := Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hM))
    (map_dvd Ideal.absNorm (primitive_redundant_dvd M C hM hC hCM))
  simpa only [map_mul] using h

lemma coprime_support_iff (I M : Ideal O) (hM : M≠0) :
    IsCoprime I M ↔ ∀P∈primeSupport M,IsCoprime I P := by
  have hprod (s : Multiset (Ideal O)) : IsCoprime I s.prod ↔ ∀P∈s,IsCoprime I P := by
    induction s using Multiset.induction_on with
    | empty => simpa using (isCoprime_one_right : IsCoprime I (1 : Ideal O))
    | cons a s ih => simp only [Multiset.prod_cons,IsCoprime.mul_right_iff,Multiset.mem_cons,
        forall_eq_or_imp,ih]
  calc
    _ ↔ IsCoprime I (normalizedFactors M).prod := by rw [Ideal.prod_normalizedFactors_eq_self hM]
    _ ↔ _ := by simpa only [primeSupport,Multiset.mem_toFinset] using hprod (normalizedFactors M)

lemma coprime_original_iff (I M C : Ideal O) (hM : M≠0) (hC : C≠0) (hCM : C∣M) :
    IsCoprime I M ↔ IsCoprime I C ∧ ∀P∈redundantSet M C,IsCoprime I P := by
  constructor
  · intro h
    refine ⟨h.of_isCoprime_of_dvd_right hCM,?_⟩
    intro P hP
    exact (coprime_support_iff I M hM).mp h P ((redundantSet_subset M C) hP)
  · rintro ⟨hIC,hIR⟩
    apply (coprime_support_iff I M hM).mpr
    intro P hP
    by_cases hPC : P∈primeSupport C
    · exact (coprime_support_iff I C hC).mp hIC P hPC
    · exact hIR P (Finset.mem_sdiff.mpr ⟨hP,hPC⟩)

theorem idealCoeff_natural_deletion (χ ψ : Character) (hmod : χ.modulus≤ψ.modulus)
    (hmask : ∀I : Ideal O,idealCoeff χ I=if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    (I : Ideal O) :
    idealCoeff χ I=idealCoeff (ψ.excludePrimes (redundantSet χ.modulus ψ.modulus)
      (redundantSet_prime χ.modulus ψ.modulus)) I := by
  rw [hmask I,idealCoeff_excludePrimes]
  have hm := coprime_original_iff I χ.modulus ψ.modulus χ.modulus_ne_bot ψ.modulus_ne_bot
    (Ideal.dvd_iff_le.mpr hmod)
  by_cases hC : IsCoprime I ψ.modulus
  · rw [hm]
    simp only [hC,true_and]
  · have hz : idealCoeff ψ I=0 := by simpa only [hC,ite_false] using idealCoeff_source_mask ψ I
    simp only [hz,ite_self]

theorem exists_natural_primitive (χ : Character) :
    ∃ψ : Character,χ.modulus≤ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (χ.residue≠1 → ψ.residue≠1) ∧
      Squarefree (redundantIdeal χ.modulus ψ.modulus) ∧
      IsCoprime (redundantIdeal χ.modulus ψ.modulus) ψ.modulus ∧
      ψ.modulus*redundantIdeal χ.modulus ψ.modulus∣χ.modulus ∧
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀I : Ideal O,idealCoeff χ I=idealCoeff
        (ψ.excludePrimes (redundantSet χ.modulus ψ.modulus)
          (redundantSet_prime χ.modulus ψ.modulus)) I := by
  obtain ⟨ψ,hmod,hprim,_,hmask⟩ := exists_primitive_character χ
  refine ⟨ψ,hmod,hprim,?_,redundantIdeal_squarefree _ _,redundantIdeal_coprime _ _ ψ.modulus_ne_bot,
    primitive_redundant_dvd _ _ χ.modulus_ne_bot ψ.modulus_ne_bot (Ideal.dvd_iff_le.mpr hmod),
    primitive_redundant_norm _ _ χ.modulus_ne_bot ψ.modulus_ne_bot (Ideal.dvd_iff_le.mpr hmod),
    idealCoeff_natural_deletion χ ψ hmod hmask⟩
  intro hχ hψ
  exact hχ ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr hψ)

end SevenEighths.CenteredMomentNaturalPrimitive
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectionDeletion
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentReflectionDeletion
open HeckeFamily CenteredMomentComparisonReflection UniqueFactorizationMonoid
open IdealMobiusDivisorSum EisensteinSchwartzPoisson ConcreteTraceCRT
local notation "O" => HeckeFamily.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma outside_iff_coprime (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) (I : NI) :
    outside S I.val ↔ ∀ P ∈ S, IsCoprime I.val P := by
  have he (P : Ideal O) (hP : Prime P) : primeSupport P = {P} := by
    simp only [primeSupport]
    have hf : normalizedFactors P = {P} := by
      simpa using normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal O)))
        (by intro Q hQ; simpa only [Multiset.mem_singleton.mp hQ] using hP)
    simp [hf]
  simp only [outside]
  apply forall_congr'
  intro P
  apply forall_congr'
  intro hP
  rw [← IdealCoprimeSieveOperator.primeSupport_disjoint_iff I.property (hS P hP).ne_zero,
    he P (hS P hP), Finset.disjoint_singleton_right]
  simp only [primeSupport, Multiset.mem_toFinset,
    mem_normalizedFactors_iff I.property, hS P hP, true_and]

lemma deleted_coefficient (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (I : NI) :
    idealCoeff (η.excludePrimes S hS) I.val =
      if outside S I.val then idealCoeff η I.val else 0 := by
  rw [idealCoeff_excludePrimes, outside_iff_coprime S hS I]
  split_ifs <;> rfl

lemma schwartz_decayTwo (W : 𝓢(ℝ,ℂ)) : DecayTwo W := by
  refine ⟨SchwartzMap.seminorm ℝ 2 0 W, apply_nonneg _ _, ?_⟩
  intro x hx
  simpa only [Real.norm_eq_abs, abs_of_pos hx] using
    SchwartzMap.norm_pow_mul_le_seminorm ℝ W 2 x

lemma reflected_decayTwo (W : 𝓢(ℝ,ℂ)) : DecayTwo (paperRadialFourier W) := by
  obtain ⟨s,C,hC,hb⟩ := paperRadialFourier_source_weighted_bound 2
  refine ⟨C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W, by positivity, ?_⟩
  intro x hx
  exact (mul_le_mul_of_nonneg_right (by nlinarith : x^2 ≤ (1+x)^2)
    (norm_nonneg _)).trans (hb W x hx.le)

lemma inverse_norm_sq_summable : Summable (fun I : NI => (norm I ^ 2)⁻¹) := by
  have h := CompletedGauss.nonzeroIdeal_norm_rpow_summable 2 (by norm_num)
  convert (preTransparency := .instances) h using 1
  funext I
  rw [Real.rpow_neg (by positivity), Real.rpow_two]
  rfl

lemma radial_summable_norm (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun I : NI => ‖F (norm I / X)‖) := by
  obtain ⟨C,hC,hb⟩ := hF
  apply (inverse_norm_sq_summable.mul_left (C*X^2)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  have hx := div_pos (norm_pos I) hX
  have h : ‖F (norm I / X)‖ ≤ C / (norm I / X)^2 :=
    (le_div_iff₀ (sq_pos_of_pos hx)).mpr (by nlinarith [hb _ hx])
  exact h.trans_eq (by field_simp)

lemma pair_radial_summable_norm (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : NI × NI => ‖F (norm p.1 * norm p.2 / X)‖) := by
  obtain ⟨C,hC,hb⟩ := hF
  have hs := inverse_norm_sq_summable.mul_of_nonneg inverse_norm_sq_summable
    (fun I => by positivity) (fun I => by positivity)
  apply (hs.mul_left (C*X^2)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro p
  have hx := div_pos (mul_pos (norm_pos p.1) (norm_pos p.2)) hX
  have h : ‖F (norm p.1 * norm p.2 / X)‖ ≤ C / (norm p.1 * norm p.2 / X)^2 :=
    (le_div_iff₀ (sq_pos_of_pos hx)).mpr (by nlinarith [hb _ hx])
  exact h.trans_eq (by field_simp)

lemma restricted_pair_summable (η : Character) (S : Finset (Ideal O))
    (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : SmoothIdeal S × OutsideIdeal S =>
      idealCoeff η (p.1.val.val * p.2.val.val) * F (norm p.1.val * norm p.2.val / X)) := by
  have hi : Function.Injective (fun p : SmoothIdeal S × OutsideIdeal S => (p.1.val,p.2.val)) := by
    intro p q h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  apply ((pair_radial_summable_norm F hF X hX).comp_injective hi).of_norm_bounded
  intro p
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η _)

lemma outside_plain_tsum (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X : ℝ) :
    (∑' I : OutsideIdeal S, idealCoeff η I.val.val * F (norm I.val / X)) =
      ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / X) := by
  have he := tsum_subtype {I : NI | outside S I.val}
    (fun I : NI => idealCoeff η I.val * F (norm I / X))
  change (∑' I : OutsideIdeal S, idealCoeff η I.val.val * F (norm I.val / X)) = _ at he
  rw [he]
  apply tsum_congr
  intro I
  rw [deleted_coefficient]
  by_cases hI : outside S I.val <;> simp [Set.indicator, hI]

lemma restoration_inner (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X : ℝ) (D : SmoothIdeal S) :
    (∑' J : OutsideIdeal S, idealCoeff η (D.val.val * J.val.val) *
      F (norm D.val * norm J.val / X)) =
    idealCoeff η D.val.val *
      ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val)) := by
  rw [← outside_plain_tsum η S hS F, ← tsum_mul_left]
  apply tsum_congr
  intro J
  rw [map_mul, mul_assoc]
  congr 2
  field_simp

lemma restoration_plain_summable (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun D : SmoothIdeal S => idealCoeff η D.val.val *
      ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val))) := by
  exact (restricted_pair_summable η S F hF X hX).prod.congr
    (fun D => restoration_inner η S hS F X D)

theorem restoration_plain (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    (∑' I : NI, idealCoeff η I.val * F (norm I / X)) =
      ∑' D : SmoothIdeal S, idealCoeff η D.val.val *
        ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val)) := by
  have he := (splitEquiv S hS).symm.tsum_eq
    (fun I : NI => idealCoeff η I.val * F (norm I / X))
  have hp := (restricted_pair_summable η S F hF X hX).tsum_prod
  have hpoint (p : SmoothIdeal S × OutsideIdeal S) :
      norm ((splitEquiv S hS).symm p) = norm p.1.val * norm p.2.val := by
    change (Ideal.absNorm (p.1.val.val * p.2.val.val) : ℝ) = _
    rw [map_mul, Nat.cast_mul]
    rfl
  simp only [hpoint] at he
  rw [← he]
  change (∑' p : SmoothIdeal S × OutsideIdeal S,
    idealCoeff η (p.1.val.val * p.2.val.val) * F (norm p.1.val * norm p.2.val / X)) = _
  rw [hp]
  exact tsum_congr (fun D => restoration_inner η S hS F X D)

lemma normalization_factor (X N : ℝ) (hX : 0<X) (hN : 0<N) :
    (Real.sqrt N : ℂ)⁻¹ * (Real.sqrt (X/N) : ℂ)⁻¹ = (Real.sqrt X : ℂ)⁻¹ := by
  rw [Real.sqrt_div hX.le, Complex.ofReal_div]
  have hn : (Real.sqrt N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hN).ne'
  field_simp

lemma normalized_restoration_term (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X : ℝ) (hX : 0<X) (D : SmoothIdeal S) :
    idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
      HeckeDyadic.polynomial (η.excludePrimes S hS) false F (X / norm D.val) 0 0 =
    (Real.sqrt X : ℂ)⁻¹ * (idealCoeff η D.val.val *
      ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val))) := by
  rw [polynomial_plain _ _ _ (div_pos hX (norm_pos D.val))]
  change idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
    ((Real.sqrt (X / norm D.val) : ℂ)⁻¹ *
    ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val))) = _
  have h := normalization_factor X (norm D.val) hX (norm_pos D.val)
  rw [div_eq_mul_inv]
  linear_combination (idealCoeff η D.val.val *
    ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val))) * h

theorem normalized_restoration (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    Summable (fun D : SmoothIdeal S => idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
      HeckeDyadic.polynomial (η.excludePrimes S hS) false F (X / norm D.val) 0 0) ∧
    HeckeDyadic.polynomial η false F X 0 0 =
      ∑' D : SmoothIdeal S, idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
        HeckeDyadic.polynomial (η.excludePrimes S hS) false F (X / norm D.val) 0 0 := by
  constructor
  · apply ((restoration_plain_summable η S hS F hF X hX).mul_left (Real.sqrt X : ℂ)⁻¹).congr
    intro D
    exact (normalized_restoration_term η S hS F X hX D).symm
  · rw [polynomial_plain _ _ _ hX]
    change (Real.sqrt X : ℂ)⁻¹ * (∑' I : NI, idealCoeff η I.val * F (norm I / X)) = _
    rw [restoration_plain η S hS F hF X hX, ← tsum_mul_left]
    apply tsum_congr
    intro D
    exact (normalized_restoration_term η S hS F X hX D).symm

lemma outsideSum_summable (η : Character) (S : Finset (Ideal O))
    (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    Summable (fun I : NI => (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X)) := by
  apply (radial_summable_norm F hF X hX).of_norm_bounded
  intro I
  split_ifs
  · rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η I.val)
  · simp

lemma outside_mul_prime (S : Finset (Ideal O)) (hS : ∀ Q ∈ S, Prime Q)
    (P : Ideal O) (hP : Prime P) (hPS : P ∉ S) (I : Ideal O) :
    outside S (P*I) ↔ outside S I := by
  have hn (Q : Ideal O) (hQ : Q ∈ S) : ¬ Q ∣ P := by
    intro hd
    have he : Q = P := associated_iff_eq.mp (((hS Q hQ).dvd_prime_iff_associated hP).mp hd)
    exact hPS (he ▸ hQ)
  simp only [outside]
  apply forall_congr'
  intro Q
  apply forall_congr'
  intro hQ
  rw [(hS Q hQ).dvd_mul, not_or, and_iff_right (hn Q hQ)]

lemma prime_shift_tsum (η : Character) (S : Finset (Ideal O))
    (hS : ∀ Q ∈ S, Prime Q) (P : Ideal O) (hP : Prime P) (hPS : P ∉ S)
    (F : ℝ → ℂ) (X : ℝ) :
    (∑' I : NI, if P ∣ I.val then
      (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X) else 0) =
    idealCoeff η P * outsideSum η S F (X / (P.absNorm : ℝ)) := by
  let f : NI → ℂ := fun I => if P ∣ I.val then
    (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X) else 0
  let g : NI → ℂ := fun I => idealCoeff η P *
    ((if outside S I.val then idealCoeff η I.val else 0) * F (norm I / (X / (P.absNorm : ℝ))))
  let e : NI → NI := fun I => ⟨P*I.val, mul_ne_zero hP.ne_zero I.property⟩
  have he (I : NI) : f (e I) = g I := by
    have hn : norm (e I) = (P.absNorm : ℝ) * norm I := by
      simp only [norm, e, map_mul, Nat.cast_mul]
    simp only [f, e, dvd_mul_right, ite_true, outside_mul_prime S hS P hP hPS,
      map_mul, g]
    change (if outside S I.val then idealCoeff η P * idealCoeff η I.val else 0) *
      F (norm (e I) / X) = _
    rw [hn]
    by_cases ho : outside S I.val
    · simp only [ho, ite_true, mul_assoc]
      congr 2
      rw [div_div_eq_mul_div, mul_comm]
    · simp [ho]
  have hi : Function.Injective e := by
    intro I J hij
    exact Subtype.ext (mul_left_cancel₀ hP.ne_zero (congrArg Subtype.val hij))
  have hsum : (∑' I, f I) = ∑' I, g I := by
    apply tsum_eq_tsum_of_ne_zero_bij (fun I : Function.support g => e I.val)
    · exact hi.comp Subtype.val_injective
    · intro I hI
      have hd : P ∣ I.val := by
        by_contra hn
        exact hI (by simp [f, hn])
      obtain ⟨J,hJ⟩ := hd
      have hj : J ≠ 0 := by intro hz; exact I.property (by rw [hJ,hz,mul_zero])
      have hei : e ⟨J,hj⟩ = I := Subtype.ext hJ.symm
      have hg : g ⟨J,hj⟩ ≠ 0 := by rw [← he, hei]; exact hI
      exact ⟨⟨⟨J,hj⟩,hg⟩,hei⟩
    · intro I; exact he I.val
  change (∑' I, f I) = _
  rw [hsum, tsum_mul_left]
  rfl

lemma outsideSum_insert (η : Character) (S : Finset (Ideal O))
    (hS : ∀ Q ∈ S, Prime Q) (P : Ideal O) (hP : Prime P) (hPS : P ∉ S)
    (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    outsideSum η (insert P S) F X = outsideSum η S F X -
      idealCoeff η P * outsideSum η S F (X / (P.absNorm : ℝ)) := by
  have hs := outsideSum_summable η S F hF X hX
  have hd : Summable (fun I : NI => if P ∣ I.val then
      (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X) else 0) := by
    exact hs.indicator {I : NI | P ∣ I.val}
  rw [← prime_shift_tsum η S hS P hP hPS F X]
  simp only [outsideSum]
  rw [← hs.tsum_sub hd]
  apply tsum_congr
  intro I
  have hi : outside (insert P S) I.val = (¬ P ∣ I.val ∧ outside S I.val) := by
    simp [outside, Finset.mem_insert]
  rw [hi]
  by_cases hp : P ∣ I.val <;> by_cases ho : outside S I.val <;>
    simp [hp, ho]

lemma subset_product_nonzero (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) :
    (∏ P ∈ S, P) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero)
lemma subset_product_norm_pos (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) :
    0 < (Ideal.absNorm (∏ P ∈ S, P) : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (subset_product_nonzero S hS))

theorem finite_deletion_plain (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    outsideSum η S F X = ∑ D ∈ S.powerset, (-1 : ℂ)^D.card * idealCoeff η (∏ P ∈ D, P) *
      (∑' I : NI, idealCoeff η I.val * F (norm I / (X / (Ideal.absNorm (∏ P ∈ D, P) : ℝ)))) := by
  induction S using Finset.induction_on generalizing X with
  | empty => simp [outsideSum, outside]
  | @insert P S hPS ih =>
    have hP := hS P (Finset.mem_insert_self _ _)
    have hSS : ∀ Q ∈ S, Prime Q := fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ)
    have hn : 0 < (P.absNorm : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero)
    rw [outsideSum_insert η S hSS P hP hPS F hF X hX,
      ih hSS X hX, ih hSS (X / (P.absNorm : ℝ)) (div_pos hX hn),
      Finset.sum_powerset_insert hPS, Finset.mul_sum]
    rw [sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro D hD
    have hPD : P ∉ D := fun h => hPS ((Finset.mem_powerset.mp hD) h)
    rw [Finset.card_insert_of_notMem hPD, Finset.prod_insert hPD, map_mul,
      map_mul, Nat.cast_mul, pow_succ]
    have hh : X / ((P.absNorm : ℝ) * (Ideal.absNorm (∏ Q ∈ D,Q) : ℝ)) =
        (X / (P.absNorm : ℝ)) / (Ideal.absNorm (∏ Q ∈ D,Q) : ℝ) := by rw [div_div]
    rw [hh]
    ring

lemma normalized_dilation_term (η : Character) (F : ℝ → ℂ) (X : ℝ)
    (hX : 0<X) (D : NI) :
    idealCoeff η D.val / (Real.sqrt (norm D) : ℂ) *
      HeckeDyadic.polynomial η false F (X / norm D) 0 0 =
    (Real.sqrt X : ℂ)⁻¹ * (idealCoeff η D.val *
      ∑' I : NI, idealCoeff η I.val * F (norm I / (X / norm D))) := by
  rw [polynomial_plain _ _ _ (div_pos hX (norm_pos D))]
  change idealCoeff η D.val / (Real.sqrt (norm D) : ℂ) *
    ((Real.sqrt (X / norm D) : ℂ)⁻¹ *
      ∑' I : NI, idealCoeff η I.val * F (norm I / (X / norm D))) = _
  have h := normalization_factor X (norm D) hX (norm_pos D)
  rw [div_eq_mul_inv]
  linear_combination (idealCoeff η D.val *
    ∑' I : NI, idealCoeff η I.val * F (norm I / (X / norm D))) * h

theorem normalized_finite_deletion (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial (η.excludePrimes S hS) false F X 0 0 =
      ∑ D ∈ S.powerset, (-1 : ℂ)^D.card *
        (idealCoeff η (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ)) *
        HeckeDyadic.polynomial η false F (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ)) 0 0 := by
  rw [polynomial_plain _ _ _ hX]
  have he : (∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F ((I.val.absNorm : ℝ) / X)) =
      outsideSum η S F X := by
    apply tsum_congr
    intro I
    rw [deleted_coefficient]
    rfl
  rw [he, finite_deletion_plain η S hS F hF X hX, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D hD
  have hDS : ∀ P ∈ D, Prime P := fun P hP => hS P ((Finset.mem_powerset.mp hD) hP)
  have ht := normalized_dilation_term η F X hX ⟨∏P∈D,P, subset_product_nonzero D hDS⟩
  dsimp only [norm] at ht
  dsimp only [norm]
  linear_combination -(-1 : ℂ)^D.card * ht

lemma subset_product_moebius (D : Finset (Ideal O)) (hD : ∀ P ∈ D, Prime P) :
    (moebius (∏ P ∈ D,P) : ℂ) = (-1 : ℂ)^D.card := by
  have hf : normalizedFactors (∏ P ∈ D,P) = D.val := by
    simpa using normalizedFactors_prod_of_prime (m := D.val) hD
  have hs : Squarefree (∏ P ∈ D,P) := by
    rw [squarefree_iff_nodup_normalizedFactors (subset_product_nonzero D hD), hf]
    exact D.nodup
  rw [hs.moebius_eq, factors_eq_normalizedFactors, hf]
  simp

theorem normalized_finite_deletion_moebius (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial (η.excludePrimes S hS) false F X 0 0 =
      ∑ D ∈ S.powerset, (moebius (∏ P ∈ D,P) : ℂ) *
        (idealCoeff η (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ)) *
        HeckeDyadic.polynomial η false F (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ)) 0 0 := by
  rw [normalized_finite_deletion η S hS F hF X hX]
  apply Finset.sum_congr rfl
  intro D hD
  rw [subset_product_moebius D (fun P hP => hS P ((Finset.mem_powerset.mp hD) hP))]

lemma reflectedTerm_eq (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X Q : ℝ)
    (D : Finset (Ideal O)) (H : SmoothIdeal S) :
    reflectedTerm η ηi S hS F X Q D H =
      ((moebius (∏ P ∈ D,P) : ℂ) *
        (idealCoeff η (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ))) *
      (idealCoeff ηi H.val.val / (Real.sqrt (norm H.val) : ℂ) *
        HeckeDyadic.polynomial (ηi.excludePrimes S hS) false F
          ((Q / (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ))) / norm H.val) 0 0) := by
  have hs : Q * (Ideal.absNorm (∏ P ∈ D,P) : ℝ) / (X * norm H.val) =
      (Q / (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ))) / norm H.val := by
    simp only [div_div_eq_mul_div, div_div]
  unfold reflectedTerm
  rw [hs, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  ring

theorem deletion_reflection (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (W F : ℝ → ℂ) (hW : DecayTwo W) (hF : DecayTwo F)
    (G : ℂ) (Q : ℝ) (hQ : 0<Q)
    (hreflect : ∀ Y : ℝ, 0<Y → HeckeDyadic.polynomial η false W Y 0 0 =
      G * HeckeDyadic.polynomial ηi false F (Q/Y) 0 0)
    (X : ℝ) (hX : 0<X) :
    (∀ D ∈ S.powerset, Summable (reflectedTerm η ηi S hS F X Q D)) ∧
    HeckeDyadic.polynomial (η.excludePrimes S hS) false W X 0 0 =
      G * ∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, reflectedTerm η ηi S hS F X Q D H := by
  have hnorm (D : Finset (Ideal O)) (hD : D ∈ S.powerset) :
      0 < (Ideal.absNorm (∏ P ∈ D,P) : ℝ) :=
    subset_product_norm_pos D (fun P hP => hS P ((Finset.mem_powerset.mp hD) hP))
  constructor
  · intro D hD
    have hs := (normalized_restoration ηi S hS F hF (Q/(X/(Ideal.absNorm (∏ P ∈ D,P) : ℝ)))
      (div_pos hQ (div_pos hX (hnorm D hD)))).1
    exact (hs.mul_left ((moebius (∏ P ∈ D,P) : ℂ) *
      (idealCoeff η (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ)))).congr
      (fun H => (reflectedTerm_eq η ηi S hS F X Q D H).symm)
  · rw [normalized_finite_deletion_moebius η S hS W hW X hX, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro D hD
    rw [hreflect _ (div_pos hX (hnorm D hD)),
      (normalized_restoration ηi S hS F hF (Q/(X/(Ideal.absNorm (∏ P ∈ D,P) : ℝ)))
        (div_pos hQ (div_pos hX (hnorm D hD)))).2]
    rw [mul_left_comm]
    congr 1
    rw [← tsum_mul_left]
    apply tsum_congr
    intro H
    rw [reflectedTerm_eq]

theorem primitive_deleted_reflection (c : O) [NeZero c]
    (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) u.val) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0<X) :
    let η := HeckePrimitive.character c χ hu
    let ηi := HeckePrimitive.character c χ⁻¹ (HeckePrimitive.inverse_unit_trivial c χ hu)
    let Q := ‖eisEmbedding c‖^2
    (∀ D ∈ S.powerset, Summable (reflectedTerm η ηi S hS (paperRadialFourier W) X Q D)) ∧
    HeckeDyadic.polynomial (η.excludePrimes S hS) false W X 0 0 =
      TraceCharacter.normalizedGauss c χ *
        ∑ D ∈ S.powerset, ∑' H : SmoothIdeal S,
          reflectedTerm η ηi S hS (paperRadialFourier W) X Q D H := by
  dsimp only
  apply deletion_reflection _ _ S hS W (paperRadialFourier W)
    (schwartz_decayTwo W) (reflected_decayTwo W) _ _ _
    (fun Y hY => primitive_normalized_reflection c χ hu hp hχ W Y hY) X hX
  exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c)))

end SevenEighths.CenteredMomentReflectionDeletion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalReflection
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentNaturalReflection
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentNaturalPrimitive
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
local instance instIsPrincipalIdealRingO_solutions : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

lemma polynomial_coeff_congr (χ ψ : Character)
    (h : ∀I,idealCoeff χ I=idealCoeff ψ I) (W : ℝ→ℂ) (X : ℝ) :
    HeckeDyadic.polynomial χ false W X 0 0=HeckeDyadic.polynomial ψ false W X 0 0 := by
  unfold HeckeDyadic.polynomial
  congr 1
  apply tsum_congr
  intro I
  unfold HeckeDyadic.summand HeckeDyadic.coefficient
  rw [h]

lemma inverse_deletion_coeff (χ ψ : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (h : ∀I,idealCoeff χ I=idealCoeff (ψ.excludePrimes S hS) I)
    (I : Ideal O) : idealCoeff χ.inverse I=idealCoeff (ψ.inverse.excludePrimes S hS) I := by
  rw [idealCoeff_inverse_conj,h,idealCoeff_excludePrimes,idealCoeff_excludePrimes,
    idealCoeff_inverse_conj]
  split_ifs <;> simp

theorem primitive_character_deleted (ψ : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals ψ.residue) (hn : ψ.residue≠1) :
    ∃G : ℂ,‖G‖=1 ∧ ∀(S : Finset (Ideal O))(hS : ∀P∈S,Prime P)
      (W : 𝓢(ℝ,ℂ))(X : ℝ),0<X →
      (∀D∈S.powerset,Summable (reflectedTerm ψ ψ.inverse S hS (paperRadialFourier W)
        X (ψ.modulus.absNorm:ℝ) D)) ∧
      HeckeDyadic.polynomial (ψ.excludePrimes S hS) false W X 0 0=
        G*∑D∈S.powerset,∑'H : SmoothIdeal S,
          reflectedTerm ψ ψ.inverse S hS (paperRadialFourier W) X (ψ.modulus.absNorm:ℝ) D H := by
  rcases ψ with ⟨M,hM,χ,hu,p,hp0,hpm⟩
  obtain ⟨c,hc⟩ := Submodule.IsPrincipal.principal M
  change M=Ideal.span {c} at hc
  subst M
  have hc0 : c≠0 := by simpa only [ne_eq,Ideal.span_singleton_eq_bot] using hM
  let : NeZero c := ⟨hc0⟩
  refine ⟨TraceCharacter.normalizedGauss c χ,TraceCharacter.normalizedGauss_norm c χ hp,?_⟩
  intro S hS W X hX
  have hh := primitive_deleted_reflection c χ hu hp hn S hS W X hX
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] at hh
  exact hh

theorem original_natural_reflection (χ : Character) (hn : χ.residue≠1) :
    ∃(ψ : Character)(G : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖G‖=1 ∧
      let S := redundantSet χ.modulus ψ.modulus
      let hS := redundantSet_prime χ.modulus ψ.modulus
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      IsCoprime (redundantIdeal χ.modulus ψ.modulus) ψ.modulus ∧
      (∀I,idealCoeff χ I=idealCoeff (ψ.excludePrimes S hS) I) ∧
      ∀(W : 𝓢(ℝ,ℂ))(X : ℝ),0<X →
        (∀D∈S.powerset,Summable (reflectedTerm ψ ψ.inverse S hS (paperRadialFourier W)
          X (ψ.modulus.absNorm:ℝ) D)) ∧
        HeckeDyadic.polynomial χ false W X 0 0=
          G*∑D∈S.powerset,∑'H : SmoothIdeal S,
            reflectedTerm ψ ψ.inverse S hS (paperRadialFourier W) X (ψ.modulus.absNorm:ℝ) D H := by
  obtain ⟨ψ,hmod,hprim,hne,hsq,hcop,hdvd,hnorm,hcoeff⟩ := exists_natural_primitive χ
  obtain ⟨G,hG,hreflection⟩ := primitive_character_deleted ψ hprim (hne hn)
  refine ⟨ψ,G,hprim,hne hn,hG,hnorm,hcop,hcoeff,?_⟩
  intro W X hX
  have hh := hreflection _ (redundantSet_prime χ.modulus ψ.modulus) W X hX
  exact ⟨hh.1,(polynomial_coeff_congr χ _ hcoeff W X).trans hh.2⟩

theorem original_inverse_reflection_oai (χ : Character) (hn : χ.residue≠1) :
    ∃(ψ : Character)(G : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖G‖=1 ∧
      let S := redundantSet χ.modulus ψ.modulus
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(W : 𝓢(ℝ,ℂ))(X : ℝ),0<X →
        HeckeDyadic.polynomial χ false W X 0 0=
          G*∑D∈S.powerset,∑'H : SmoothIdeal S,
            (UniqueFactorizationMonoid.moebius (∏P∈D,P):ℂ)*idealCoeff ψ (∏P∈D,P)*
              idealCoeff ψ.inverse H.val.val /
              (Real.sqrt ((Ideal.absNorm (∏P∈D,P):ℝ)*norm H.val):ℂ)*
              HeckeDyadic.polynomial χ.inverse false (paperRadialFourier W)
                ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0 := by
  obtain ⟨ψ,G,hprim,hne,hG,hnorm,hcop,hcoeff,hreflect⟩ := original_natural_reflection χ hn
  refine ⟨ψ,G,hprim,hne,hG,hnorm,?_⟩
  intro W X hX
  rw [(hreflect W X hX).2]
  congr 1
  apply Finset.sum_congr rfl
  intro D hD
  apply tsum_congr
  intro H
  unfold reflectedTerm
  rw [←polynomial_coeff_congr χ.inverse _
    (inverse_deletion_coeff χ ψ _ (redundantSet_prime χ.modulus ψ.modulus) hcoeff)]

end SevenEighths.CenteredMomentNaturalReflection

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.CenteredMomentNaturalReflection.original_inverse_reflection_oai := @OAI.SevenEighths.CenteredMomentNaturalReflection.original_inverse_reflection_oai
