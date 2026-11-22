-- Prove2me | solution 1 for LCAGroup.L1_convolution_commutative_algebra
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:35:06.225665+00:00
-- url     : https://prove2.me/submissions/1ab173a6-5c8e-48b8-9f10-441659544cfa

import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution
import Theorems.Thm_LCAGroup_fourier_convolution
import Theorems.Thm_LCAGroup_fourier_L1_to_zeroAtInfty_injective

open MeasureTheory Topology
open scoped ZeroAtInfty

set_option autoImplicit false

namespace Sol_LCAGroup_L1_convolution_commutative_algebra

open RiemannMasullo

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- Pointwise commutativity of the convolution (substitution `y ↦ x / y`). -/
lemma conv_comm (f g : G → ℂ) (x : G) :
    lcaConvolution μ f g x = lcaConvolution μ g f x := by
  unfold lcaConvolution
  have h := integral_div_left_eq_self (fun y : G => f y * g (y⁻¹ * x)) μ x
  rw [← h]
  congr 1
  funext y
  have h1 : (x / y)⁻¹ * x = y := by
    rw [inv_div, div_mul_cancel]
  rw [h1, mul_comm, div_eq_mul_inv, mul_comm x y⁻¹]

/-- The convolution only depends on the a.e. class of its first argument. -/
lemma conv_congr_left {f f' : G → ℂ} (h : f =ᵐ[μ] f') (g : G → ℂ) :
    lcaConvolution μ f g = lcaConvolution μ f' g := by
  funext x
  unfold lcaConvolution
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

/-- The convolution only depends on the a.e. classes of its arguments. -/
lemma conv_congr {f f' g g' : G → ℂ} (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
    lcaConvolution μ f g = lcaConvolution μ f' g' := by
  rw [conv_congr_left μ hf g]
  have e1 : lcaConvolution μ f' g = lcaConvolution μ g f' := funext (conv_comm μ f' g)
  have e2 : lcaConvolution μ f' g' = lcaConvolution μ g' f' := funext (conv_comm μ f' g')
  rw [e1, e2, conv_congr_left μ hg f']

lemma conv_add_left (f₁ f₂ g : G → ℂ) (h1 : Integrable f₁ μ) (h2 : Integrable f₂ μ)
    (hg : Integrable g μ) :
    lcaConvolution μ (f₁ + f₂) g =ᵐ[μ] lcaConvolution μ f₁ g + lcaConvolution μ f₂ g := by
  filter_upwards [(LCAGroup.fourier_convolution G μ f₁ g h1 hg).1,
    (LCAGroup.fourier_convolution G μ f₂ g h2 hg).1] with x hx1 hx2
  simp only [lcaConvolution, Pi.add_apply, add_mul]
  exact integral_add hx1 hx2

lemma conv_smul_left (c : ℂ) (f g : G → ℂ) :
    lcaConvolution μ (c • f) g = c • lcaConvolution μ f g := by
  funext x
  simp only [lcaConvolution, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

/-- The convolution of two `L¹` classes, as an `L¹` class. -/
noncomputable def mul (f g : Lp ℂ 1 μ) : Lp ℂ 1 μ :=
  (LCAGroup.fourier_convolution G μ f g (L1.integrable_coeFn f)
    (L1.integrable_coeFn g)).2.1.toL1 _

lemma coeFn_mul (f g : Lp ℂ 1 μ) :
    (mul μ f g : G → ℂ) =ᵐ[μ] lcaConvolution μ (f : G → ℂ) (g : G → ℂ) :=
  Integrable.coeFn_toL1 _

lemma mul_comm' (f g : Lp ℂ 1 μ) : mul μ f g = mul μ g f := by
  apply Lp.ext
  filter_upwards [coeFn_mul μ f g, coeFn_mul μ g f] with x h1 h2
  rw [h1, h2, conv_comm]

lemma mul_add_left (f₁ f₂ g : Lp ℂ 1 μ) : mul μ (f₁ + f₂) g = mul μ f₁ g + mul μ f₂ g := by
  apply Lp.ext
  have hc : lcaConvolution μ ((f₁ + f₂ : Lp ℂ 1 μ) : G → ℂ) (g : G → ℂ) =
      lcaConvolution μ ((f₁ : G → ℂ) + (f₂ : G → ℂ)) (g : G → ℂ) :=
    conv_congr_left μ (Lp.coeFn_add f₁ f₂) _
  filter_upwards [coeFn_mul μ (f₁ + f₂) g, Lp.coeFn_add (mul μ f₁ g) (mul μ f₂ g),
    coeFn_mul μ f₁ g, coeFn_mul μ f₂ g,
    conv_add_left μ (f₁ : G → ℂ) (f₂ : G → ℂ) (g : G → ℂ) (L1.integrable_coeFn f₁)
      (L1.integrable_coeFn f₂) (L1.integrable_coeFn g)] with x h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h3, h4, hc, h5, Pi.add_apply]

lemma mul_smul_left (c : ℂ) (f g : Lp ℂ 1 μ) : mul μ (c • f) g = c • mul μ f g := by
  apply Lp.ext
  have hc : lcaConvolution μ ((c • f : Lp ℂ 1 μ) : G → ℂ) (g : G → ℂ) =
      lcaConvolution μ (c • (f : G → ℂ)) (g : G → ℂ) :=
    conv_congr_left μ (Lp.coeFn_smul c f) _
  filter_upwards [coeFn_mul μ (c • f) g, Lp.coeFn_smul c (mul μ f g),
    coeFn_mul μ f g] with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3, hc, conv_smul_left, Pi.smul_apply]

lemma mul_add_right (f g₁ g₂ : Lp ℂ 1 μ) : mul μ f (g₁ + g₂) = mul μ f g₁ + mul μ f g₂ := by
  rw [mul_comm' μ f, mul_comm' μ f, mul_comm' μ f, mul_add_left]

lemma mul_smul_right (c : ℂ) (f g : Lp ℂ 1 μ) : mul μ f (c • g) = c • mul μ f g := by
  rw [mul_comm' μ f, mul_comm' μ f, mul_smul_left]

lemma norm_mul_le (f g : Lp ℂ 1 μ) : ‖mul μ f g‖ ≤ ‖f‖ * ‖g‖ := by
  have h := (LCAGroup.fourier_convolution G μ f g (L1.integrable_coeFn f)
    (L1.integrable_coeFn g)).2.2.1
  unfold mul
  rw [L1.norm_of_fun_eq_integral_norm, L1.norm_eq_integral_norm f, L1.norm_eq_integral_norm g]
  exact h

/-- The Fourier transform of a convolution of `L¹` classes. -/
lemma fourier_mul (f g : Lp ℂ 1 μ) (χ : PontryaginDual G) :
    lcaFourier μ (mul μ f g : G → ℂ) χ = lcaFourier μ (f : G → ℂ) χ * lcaFourier μ (g : G → ℂ) χ := by
  have h1 : lcaFourier μ (mul μ f g : G → ℂ) χ =
      lcaFourier μ (lcaConvolution μ (f : G → ℂ) (g : G → ℂ)) χ := by
    unfold lcaFourier
    apply integral_congr_ae
    filter_upwards [coeFn_mul μ f g] with x hx
    rw [hx]
  rw [h1]
  exact (LCAGroup.fourier_convolution G μ f g (L1.integrable_coeFn f)
    (L1.integrable_coeFn g)).2.2.2 χ

end Sol_LCAGroup_L1_convolution_commutative_algebra

open Sol_LCAGroup_L1_convolution_commutative_algebra in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    ∃ m : Lp ℂ 1 μ →ₗ[ℂ] Lp ℂ 1 μ →ₗ[ℂ] Lp ℂ 1 μ,
      (∀ f g : Lp ℂ 1 μ,
        (m f g : G → ℂ) =ᵐ[μ] RiemannMasullo.lcaConvolution μ (f : G → ℂ) (g : G → ℂ)) ∧
      (∀ f g : Lp ℂ 1 μ, m f g = m g f) ∧
      (∀ f g h : Lp ℂ 1 μ, m (m f g) h = m f (m g h)) ∧
      ∀ f g : Lp ℂ 1 μ, ‖m f g‖ ≤ ‖f‖ * ‖g‖ := by
  obtain ⟨F, hF, hFinj, -⟩ := LCAGroup.fourier_L1_to_zeroAtInfty_injective G μ
  refine ⟨LinearMap.mk₂ ℂ (mul μ) (mul_add_left μ) (mul_smul_left μ) (mul_add_right μ)
    (mul_smul_right μ), ?_, ?_, ?_, ?_⟩
  · intro f g
    exact coeFn_mul μ f g
  · intro f g
    exact mul_comm' μ f g
  · intro f g h
    show mul μ (mul μ f g) h = mul μ f (mul μ g h)
    apply hFinj
    ext χ
    rw [hF, hF, fourier_mul, fourier_mul, fourier_mul, fourier_mul, mul_assoc]
  · intro f g
    exact norm_mul_le μ f g
