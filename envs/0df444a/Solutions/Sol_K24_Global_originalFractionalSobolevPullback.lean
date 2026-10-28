-- Prove2me | solution 1 for K24.Global.originalFractionalSobolevPullback
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-26T05:31:54.316005+00:00
-- url     : https://prove2.me/submissions/9e4eb3d8-11be-46bb-af77-39283cec05d7

import Definitions.Def_K24GlobalStatement
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

set_option autoImplicit false


/- Inlined source K24SOBCOMPOSE_ChangeVariables.lean; SHA256 dab76a3456eebc918dc8fcaf1b0fd4e6ea9d9e8b1119c6da5ff55b4bcc44f03b. -/
noncomputable section K24SOBCOMPOSE_ChangeVariables_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace K24.Global.SobolevComposition

/-- Actual fractional difference energy on a measurable coordinate domain.
The diagonal is assigned the ordinary totalized zero value; every quantity is
computed from the original pointwise function, before a Bessel comparison. -/
def fractionalDifferenceEnergy (α : ℝ) (U : Set FourSpace) (f : FourSpace → ℂ) : ℝ≥0∞ :=
  ∫⁻ x in U, ∫⁻ y in U,
    ENNReal.ofReal (‖f x-f y‖ ^ (2 : ℕ) / ‖x-y‖ ^ ((4 : ℝ) + 2*α))

/-- A genuine differentiable injective coordinate map with the displayed
actual Jacobian lower bound controls pullback of every nonnegative integrand.
The domination is proved by the Jacobian change-of-variables theorem. -/
theorem lintegral_comp_le_of_jacobian
    (U : Set FourSpace) (hU : MeasurableSet U)
    (φ : FourSpace → FourSpace) (Dφ : FourSpace → FourSpace →L[ℝ] FourSpace)
    (hd : ∀ x ∈ U, HasFDerivWithinAt φ (Dφ x) U x) (hi : InjOn φ U)
    (J : ℝ≥0) (hJ : ∀ x ∈ U, (1 : ℝ≥0∞) ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(Dφ x).det|)
    (g : FourSpace → ℝ≥0∞) :
    (∫⁻ x in U, g (φ x)) ≤ (J : ℝ≥0∞) * ∫⁻ x in φ '' U, g x := by
  calc
    _ ≤ ∫⁻ x in U, (J : ℝ≥0∞) * (ENNReal.ofReal |(Dφ x).det| * g (φ x)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hU] with x hx
      simpa only [one_mul, mul_assoc] using mul_le_mul (hJ x hx) (le_refl (g (φ x))) bot_le bot_le
    _ = (J : ℝ≥0∞) * ∫⁻ x in U, ENNReal.ofReal |(Dφ x).det| * g (φ x) :=
      lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ = _ := by
      rw [← lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hU hd hi g]

/-- The two-variable Jacobian factor is obtained by two actual changes of
variables. No measure-domination or composition-bound premise is assumed. -/
theorem lintegral_comp_pair_le_of_jacobian
    (U : Set FourSpace) (hU : MeasurableSet U)
    (φ : FourSpace → FourSpace) (Dφ : FourSpace → FourSpace →L[ℝ] FourSpace)
    (hd : ∀ x ∈ U, HasFDerivWithinAt φ (Dφ x) U x) (hi : InjOn φ U)
    (J : ℝ≥0) (hJ : ∀ x ∈ U, (1 : ℝ≥0∞) ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(Dφ x).det|)
    (g : FourSpace → FourSpace → ℝ≥0∞) :
    (∫⁻ x in U, ∫⁻ y in U, g (φ x) (φ y)) ≤
      (J : ℝ≥0∞) ^ (2 : ℕ) * ∫⁻ x in φ '' U, ∫⁻ y in φ '' U, g x y := by
  calc
    _ ≤ ∫⁻ x in U, (J : ℝ≥0∞) * ∫⁻ y in φ '' U, g (φ x) y := by
      apply lintegral_mono
      intro x
      exact lintegral_comp_le_of_jacobian U hU φ Dφ hd hi J hJ (g (φ x))
    _ = (J : ℝ≥0∞) * ∫⁻ x in U, ∫⁻ y in φ '' U, g (φ x) y :=
      lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ ≤ (J : ℝ≥0∞) * ((J : ℝ≥0∞) * ∫⁻ x in φ '' U, ∫⁻ y in φ '' U, g x y) := by
      apply mul_le_mul (le_refl _) _ bot_le bot_le
      exact lintegral_comp_le_of_jacobian U hU φ Dφ hd hi J hJ
        (fun x => ∫⁻ y in φ '' U, g x y)
    _ = _ := by ring

/-- Pointwise distortion of the genuine fractional difference kernel under
an arbitrary Lipschitz coordinate map. This is not restricted to affine maps. -/
theorem fractional_kernel_comp_le (p : ℝ) (hp : 0 ≤ p)
    (f : FourSpace → ℂ) (φ : FourSpace → FourSpace)
    (L : ℝ≥0) (x y : FourSpace)
    (hlip : ‖φ x-φ y‖ ≤ (L : ℝ) * ‖x-y‖) :
    ‖f (φ x)-f (φ y)‖ ^ (2 : ℕ) / ‖x-y‖ ^ p ≤
      (L : ℝ) ^ p * (‖f (φ x)-f (φ y)‖ ^ (2 : ℕ) / ‖φ x-φ y‖ ^ p) := by
  by_cases heq : φ x = φ y
  · simp [heq]
  have hxy : x ≠ y := by intro h; subst y; exact heq rfl
  have hs : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have ht : 0 < ‖φ x-φ y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr heq)
  have hpow : ‖φ x-φ y‖ ^ p ≤ (L : ℝ) ^ p * ‖x-y‖ ^ p := by
    calc
      _ ≤ ((L : ℝ) * ‖x-y‖) ^ p := Real.rpow_le_rpow (norm_nonneg _) hlip hp
      _ = _ := Real.mul_rpow L.coe_nonneg (norm_nonneg _)
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hs p) (Real.rpow_pos_of_pos ht p)).mpr
  calc
    _ ≤ ‖f (φ x)-f (φ y)‖ ^ (2 : ℕ) * ((L : ℝ) ^ p * ‖x-y‖ ^ p) :=
      mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
    _ = _ := by ring

/-- A nonlinear coordinate pullback bound for the actual fractional
Gagliardo difference energy. The Jacobian premise concerns the genuine
Fréchet derivative, and the exponent remains the original arbitrary real α. -/
theorem fractionalDifferenceEnergy_comp_le
    (α : ℝ) (hα : 0 < α) (U : Set FourSpace) (hU : MeasurableSet U)
    (φ : FourSpace → FourSpace) (Dφ : FourSpace → FourSpace →L[ℝ] FourSpace)
    (hd : ∀ x ∈ U, HasFDerivWithinAt φ (Dφ x) U x) (hi : InjOn φ U)
    (J L : ℝ≥0)
    (hJ : ∀ x ∈ U, (1 : ℝ≥0∞) ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(Dφ x).det|)
    (hL : ∀ x ∈ U, ∀ y ∈ U, ‖φ x-φ y‖ ≤ (L : ℝ) * ‖x-y‖)
    (f : FourSpace → ℂ) :
    fractionalDifferenceEnergy α U (f ∘ φ) ≤
      ENNReal.ofReal ((L : ℝ) ^ ((4 : ℝ)+2*α)) * (J : ℝ≥0∞) ^ (2 : ℕ) *
        fractionalDifferenceEnergy α (φ '' U) f := by
  let K : ℝ≥0∞ := ENNReal.ofReal ((L : ℝ) ^ ((4 : ℝ)+2*α))
  let g : FourSpace → FourSpace → ℝ≥0∞ := fun x y =>
    ENNReal.ofReal (‖f x-f y‖ ^ (2 : ℕ) / ‖x-y‖ ^ ((4 : ℝ)+2*α))
  have hpoint (x : FourSpace) (hx : x ∈ U) (y : FourSpace) (hy : y ∈ U) :
      ENNReal.ofReal (‖f (φ x)-f (φ y)‖ ^ (2 : ℕ) / ‖x-y‖ ^ ((4 : ℝ)+2*α)) ≤
        K * g (φ x) (φ y) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (fractional_kernel_comp_le _ (by linarith) f φ L x y (hL x hx y hy))
  unfold fractionalDifferenceEnergy
  calc
    _ ≤ ∫⁻ x in U, ∫⁻ y in U, K * g (φ x) (φ y) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hU] with x hx
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hU] with y hy
      exact hpoint x hx y hy
    _ = K * ∫⁻ x in U, ∫⁻ y in U, g (φ x) (φ y) := by
      simp_rw [lintegral_const_mul' K _ ENNReal.ofReal_ne_top]
    _ ≤ K * ((J : ℝ≥0∞) ^ (2 : ℕ) * ∫⁻ x in φ '' U, ∫⁻ y in φ '' U, g x y) :=
      mul_le_mul (le_refl _)
        (lintegral_comp_pair_le_of_jacobian U hU φ Dφ hd hi J hJ g) bot_le bot_le
    _ = _ := by rw [mul_assoc]

end K24.Global.SobolevComposition
end K24SOBCOMPOSE_ChangeVariables_Bundle


/- Inlined source K24SOBCOMPOSE_Kernel.lean; SHA256 29a462d7f25539b1fbdbff11732bdf3f42b7db102f33cf09206ef7f9fc826f88. -/
noncomputable section K24SOBCOMPOSE_Kernel_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology RealInnerProductSpace
namespace K24.Global.SobolevComposition

/-- The genuine Fourier difference multiplier, with Mathlib's 2π convention. -/
def fractionalFourierDensity (α : ℝ) (ξ h : FourSpace) : ℝ :=
  ‖(Real.fourierChar (inner ℝ h ξ) : ℂ) - 1‖ ^ (2 : ℕ) /
    ‖h‖ ^ ((4 : ℝ) + 2 * α)

/-- The frequency kernel obtained by Tonelli from the actual translation energy. -/
def fractionalFourierKernel (α : ℝ) (ξ : FourSpace) : ℝ≥0∞ :=
  ∫⁻ h : FourSpace, ENNReal.ofReal (fractionalFourierDensity α ξ h)

theorem fractionalFourierDensity_nonneg (α : ℝ) (ξ h : FourSpace) :
    0 ≤ fractionalFourierDensity α ξ h := by
  unfold fractionalFourierDensity
  positivity

theorem fractionalFourierDensity_measurable (α : ℝ) (ξ : FourSpace) :
    Measurable (fractionalFourierDensity α ξ) := by
  unfold fractionalFourierDensity
  fun_prop

@[simp] theorem fractionalFourierKernel_zero (α : ℝ) :
    fractionalFourierKernel α 0 = 0 := by
  simp [fractionalFourierKernel, fractionalFourierDensity]

theorem fractionalFourierKernel_isometry (α : ℝ)
    (e : FourSpace ≃ₗᵢ[ℝ] FourSpace) (ξ : FourSpace) :
    fractionalFourierKernel α (e ξ) = fractionalFourierKernel α ξ := by
  unfold fractionalFourierKernel
  rw [← e.measurePreserving.lintegral_comp_emb e.toMeasurableEquiv.measurableEmbedding]
  apply lintegral_congr
  intro h
  simp only [fractionalFourierDensity, e.inner_map_map, e.norm_map]

theorem fractionalFourierKernel_norm_eq (α : ℝ) (ξ η : FourSpace)
    (h : ‖ξ‖ = ‖η‖) :
    fractionalFourierKernel α ξ = fractionalFourierKernel α η := by
  let e : FourSpace ≃ₗᵢ[ℝ] FourSpace := (ℝ ∙ (ξ - η))ᗮ.reflection
  have he : e ξ = η := Submodule.reflection_sub h
  rw [← he]
  exact (fractionalFourierKernel_isometry α e ξ).symm

theorem fourierChar_sub_one_norm_le (t : ℝ) :
    ‖(Real.fourierChar t : ℂ) - 1‖ ≤ 2 * Real.pi * |t| := by
  rw [Real.fourierChar_apply]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * t)
  simpa only [mul_comm Complex.I, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)] using h

theorem fourierChar_sub_one_norm_le_two (t : ℝ) :
    ‖(Real.fourierChar t : ℂ) - 1‖ ≤ 2 := by
  calc
    _ ≤ ‖(Real.fourierChar t : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num

end K24.Global.SobolevComposition
end K24SOBCOMPOSE_Kernel_Bundle


/- Inlined source K24SOBCOMPOSE_KernelScaling.lean; SHA256 d7934b53571fae74fdeaef52109fbd3b9ef784ad3b3ca823b0f6f41d1f2d0e24. -/
noncomputable section K24SOBCOMPOSE_KernelScaling_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology RealInnerProductSpace
namespace K24.Global.SobolevComposition

theorem fractionalFourierDensity_smul (α c : ℝ) (hc : 0 < c) (ξ h : FourSpace) :
    fractionalFourierDensity α (c • ξ) h =
      c ^ ((4 : ℝ)+2*α) * fractionalFourierDensity α ξ (c • h) := by
  unfold fractionalFourierDensity
  rw [real_inner_smul_right, real_inner_smul_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos hc, Real.mul_rpow hc.le (norm_nonneg _)]
  field_simp [(Real.rpow_pos_of_pos hc ((4 : ℝ)+2*α)).ne']

theorem fractionalFourierKernel_smul (α c : ℝ) (hc : 0 < c) (ξ : FourSpace) :
    fractionalFourierKernel α (c • ξ) =
      ENNReal.ofReal (c ^ (2*α)) * fractionalFourierKernel α ξ := by
  have hmap : (∫⁻ h : FourSpace,
      ENNReal.ofReal (fractionalFourierDensity α ξ (c • h))) =
      ENNReal.ofReal ((c ^ (4 : ℕ))⁻¹) * fractionalFourierKernel α ξ := by
    rw [← lintegral_map (fractionalFourierDensity_measurable α ξ).ennreal_ofReal
      (by fun_prop : Measurable (fun h : FourSpace => c • h))]
    rw [Measure.map_addHaar_smul volume hc.ne', lintegral_smul_measure]
    simp [FourSpace, abs_of_pos (inv_pos.mpr (pow_pos hc 4)), fractionalFourierKernel]
  unfold fractionalFourierKernel
  simp_rw [fractionalFourierDensity_smul α c hc ξ,
    ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hmap, ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _)]
  congr 2
  rw [← div_eq_mul_inv, ← Real.rpow_natCast c 4, ← Real.rpow_sub hc]
  congr 1
  ring

theorem fractionalFourierKernel_radial (α : ℝ) (hα : 0 < α) (ξ : FourSpace) :
    fractionalFourierKernel α ξ =
      fractionalFourierKernel α (basisVector 0) * ENNReal.ofReal (‖ξ‖ ^ (2*α)) := by
  by_cases hξ : ξ = 0
  · simp [hξ, Real.zero_rpow (by positivity : 2*α ≠ 0)]
  have hnorm : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hb : ‖basisVector (0 : Fin 4)‖ = 1 := by simp [basisVector]
  calc
    _ = fractionalFourierKernel α (‖ξ‖ • basisVector 0) := by
      apply fractionalFourierKernel_norm_eq
      simp [norm_smul, hb, abs_of_pos hnorm]
    _ = _ := by rw [fractionalFourierKernel_smul α ‖ξ‖ hnorm]; exact mul_comm _ _

end K24.Global.SobolevComposition
end K24SOBCOMPOSE_KernelScaling_Bundle


/- Inlined source K24SOBCOMPOSE_KernelFinite.lean; SHA256 e32cacfd41a87f8340d2363ad6ca81aef6119739c5b00102320f2b5dbbddd575. -/
noncomputable section K24SOBCOMPOSE_KernelFinite_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology RealInnerProductSpace
namespace K24.Global.SobolevComposition

theorem fractionalFourierDensity_le_near (α : ℝ) (ξ h : FourSpace) :
    fractionalFourierDensity α ξ h ≤
      (2*Real.pi*‖ξ‖)^2 * ‖h‖ ^ (-(2+2*α)) := by
  by_cases hh : h = 0
  · simp [hh, fractionalFourierDensity]
    positivity
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hp : ‖(Real.fourierChar (inner ℝ h ξ) : ℂ)-1‖ ≤
      (2*Real.pi*‖ξ‖)*‖h‖ := by
    calc
      _ ≤ 2*Real.pi*|inner ℝ h ξ| := fourierChar_sub_one_norm_le _
      _ ≤ 2*Real.pi*(‖h‖*‖ξ‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm h ξ) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ((2*Real.pi*‖ξ‖)*‖h‖)^2 / ‖h‖ ^ ((4:ℝ)+2*α) := by
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hp 2)
        (Real.rpow_nonneg hn.le _)
    _ = _ := by
      rw [mul_pow, mul_div_assoc, ← Real.rpow_natCast ‖h‖ 2, ← Real.rpow_sub hn]
      congr 2
      ring

theorem fractionalFourierDensity_le_far (α : ℝ) (ξ h : FourSpace) :
    fractionalFourierDensity α ξ h ≤ 4 * ‖h‖ ^ (-((4:ℝ)+2*α)) := by
  have hp := pow_le_pow_left₀ (norm_nonneg ((Real.fourierChar (inner ℝ h ξ) : ℂ)-1))
    (fourierChar_sub_one_norm_le_two (inner ℝ h ξ)) 2
  calc
    _ ≤ 4 / ‖h‖ ^ ((4:ℝ)+2*α) := by
      unfold fractionalFourierDensity
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
      norm_num at hp ⊢
      exact hp
    _ = _ := by rw [Real.rpow_neg (norm_nonneg _)]; rfl

theorem fractionalFourierDensity_integrable (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (ξ : FourSpace) : Integrable (fractionalFourierDensity α ξ) := by
  have hm : AEStronglyMeasurable (fractionalFourierDensity α ξ) volume :=
    (fractionalFourierDensity_measurable α ξ).aestronglyMeasurable
  have hnear : IntegrableOn (fractionalFourierDensity α ξ) (Metric.ball 0 1) := by
    apply integrableOn_ball_of_norm_le_rpow (by simp [FourSpace])
      (C := (2*Real.pi*‖ξ‖)^2) (α := 2+2*α)
    · simp only [FourSpace, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]
      linarith
    · exact Filter.Eventually.of_forall (fun h => by
        rw [Real.norm_eq_abs, abs_of_nonneg (fractionalFourierDensity_nonneg α ξ h)]
        exact fractionalFourierDensity_le_near α ξ h)
    · exact hm
  have htail : IntegrableOn (fractionalFourierDensity α ξ) (Metric.ball 0 1)ᶜ := by
    have hdim : (Module.finrank ℝ FourSpace : ℝ) < (4:ℝ)+2*α := by
      simp only [FourSpace, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]
      linarith
    have hi := ((integrable_one_add_norm (μ := (volume : Measure FourSpace)) hdim).const_mul
      (4 * (2:ℝ)^((4:ℝ)+2*α))).integrableOn (s := (Metric.ball 0 1)ᶜ)
    apply hi.mono' hm.restrict
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with h hh
    have hn : 1 ≤ ‖h‖ := by simpa using hh
    rw [Real.norm_eq_abs, abs_of_nonneg (fractionalFourierDensity_nonneg α ξ h)]
    have hp : 0 ≤ (4:ℝ)+2*α := by linarith
    have hdec := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (1+‖h‖)/2)
      (by linarith : (1+‖h‖)/2 ≤ ‖h‖) (neg_nonpos.mpr hp)
    calc
      _ ≤ 4 * ‖h‖ ^ (-((4:ℝ)+2*α)) := fractionalFourierDensity_le_far α ξ h
      _ ≤ 4 * ((1+‖h‖)/2) ^ (-((4:ℝ)+2*α)) := mul_le_mul_of_nonneg_left hdec (by norm_num)
      _ = _ := by
        rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
          div_eq_mul_inv, inv_inv]
        ring
  have hu := integrableOn_union.mpr ⟨hnear, htail⟩
  simpa only [union_compl_self, integrableOn_univ] using hu

theorem fractionalFourierKernel_lt_top (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (ξ : FourSpace) : fractionalFourierKernel α ξ < ⊤ := by
  unfold fractionalFourierKernel
  rw [← ofReal_integral_eq_lintegral_ofReal (fractionalFourierDensity_integrable α hα hα1 ξ)
    (Filter.Eventually.of_forall (fractionalFourierDensity_nonneg α ξ))]
  exact ENNReal.ofReal_lt_top

end K24.Global.SobolevComposition
end K24SOBCOMPOSE_KernelFinite_Bundle


/- Inlined source K24SOBCOMPOSE_KernelPositive.lean; SHA256 9a06c660a6470c959a6807225011659b8a8e980e9eae67ab29f2eff099cd5e46. -/
noncomputable section K24SOBCOMPOSE_KernelPositive_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology RealInnerProductSpace
namespace K24.Global.SobolevComposition

theorem fractionalFourierDensity_continuousAt (α : ℝ) (ξ h : FourSpace) (hh : h ≠ 0) :
    ContinuousAt (fractionalFourierDensity α ξ) h := by
  have hn : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh
  unfold fractionalFourierDensity
  apply ContinuousAt.div
  · fun_prop
  · exact continuous_norm.continuousAt.rpow_const (Or.inl hn)
  · exact (Real.rpow_pos_of_pos (norm_pos_iff.mpr hh) _).ne'

theorem fractionalFourierKernel_basis_pos (α : ℝ) :
    0 < fractionalFourierKernel α (basisVector 0) := by
  let e : FourSpace := basisVector 0
  let h : FourSpace := (1/2 : ℝ) • e
  have he : ‖e‖ = 1 := by simp [e, basisVector]
  have hn : ‖h‖ = (1/2 : ℝ) := by simp [h, norm_smul, he]
  have hh : h ≠ 0 := by intro hz; rw [hz, norm_zero] at hn; norm_num at hn
  have hip : inner ℝ h e = (1/2 : ℝ) := by
    rw [show h = (1/2:ℝ) • e from rfl, real_inner_smul_left,
      real_inner_self_eq_norm_sq, he]
    norm_num
  have hc : (Real.fourierChar (1/2 : ℝ) : ℂ) ≠ 1 := by
    have hphase : Real.fourierChar (1/2 : ℝ) ≠ (1 : Circle) := by
      rw [Real.fourierChar_apply', show 2*Real.pi*(1/2:ℝ) = Real.pi by ring]
      exact Circle.exp_pi_ne_one
    intro hz
    apply hphase
    exact Subtype.ext hz
  have hd : 0 < fractionalFourierDensity α e h := by
    unfold fractionalFourierDensity
    rw [hip, hn]
    exact div_pos (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hc)) 2)
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hcont := fractionalFourierDensity_continuousAt α e h hh
  have hnhds : {x | 0 < fractionalFourierDensity α e x} ∈ 𝓝 h :=
    hcont.preimage_mem_nhds (Ioi_mem_nhds hd)
  unfold fractionalFourierKernel
  apply (lintegral_pos_iff_support (fractionalFourierDensity_measurable α e).ennreal_ofReal).mpr
  apply Measure.measure_pos_of_mem_nhds
  apply Filter.mem_of_superset hnhds
  intro x hx
  exact (ENNReal.ofReal_pos.mpr hx).ne'

/-- The actual Fourier difference kernel has a finite strictly positive
normalization, for every real fractional exponent between zero and one. -/
theorem fractionalFourierKernel_characterization (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ ξ : FourSpace,
      fractionalFourierKernel α ξ = (c : ℝ≥0∞) * ENNReal.ofReal (‖ξ‖ ^ (2*α)) := by
  let c := (fractionalFourierKernel α (basisVector 0)).toNNReal
  have hfin := (fractionalFourierKernel_lt_top α hα hα1 (basisVector 0)).ne
  have hc : (c : ℝ≥0∞) = fractionalFourierKernel α (basisVector 0) :=
    ENNReal.coe_toNNReal hfin
  refine ⟨c, ?_, ?_⟩
  · exact ENNReal.coe_pos.mp (hc ▸ fractionalFourierKernel_basis_pos α)
  · intro ξ
    rw [hc]
    exact fractionalFourierKernel_radial α hα ξ

end K24.Global.SobolevComposition
end K24SOBCOMPOSE_KernelPositive_Bundle


/- Inlined source K24SOBFRACTIONAL_Translation.lean; SHA256 5a5553237401456360c48d7df5faacadcea3935786fcd925c18b38c6030a8f2d. -/
noncomputable section K24SOBFRACTIONAL_Translation_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 16
open MeasureTheory FourierTransform Filter
open scoped ENNReal NNReal SchwartzMap Topology

namespace K24.Global.SobolevFractional

/-- Actual translation of L2 equivalence classes, with the plus convention. -/
def translateL2 (h : FourSpace) : LocalL2 →L[ℂ] LocalL2 :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x : FourSpace => x + h)
    (measurePreserving_add_right volume h)).toContinuousLinearMap

theorem translateL2_ae (h : FourSpace) (v : LocalL2) :
    translateL2 h v =ᵐ[volume] fun x => v (x + h) :=
  Lp.coeFn_compMeasurePreserving _ _

def phase (h ξ : FourSpace) : ℂ := (Real.fourierChar (inner ℝ h ξ) : ℂ)

theorem continuous_phase (h : FourSpace) : Continuous (phase h) :=
  (continuous_subtype_val.comp Real.continuous_fourierChar).comp (by fun_prop)

theorem phase_memLp_top (h : FourSpace) : MemLp (phase h) ∞ volume := by
  apply memLp_top_of_bound (continuous_phase h).aestronglyMeasurable 1
  exact ae_of_all _ (fun ξ => by simp [phase])

/-- The bounded phase multiplier on actual L2 classes. -/
def modulateL2 (h : FourSpace) : LocalL2 →L[ℂ] LocalL2 :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2
    ((phase_memLp_top h).toLp (phase h))

theorem modulateL2_ae (h : FourSpace) (v : LocalL2) :
    modulateL2 h v =ᵐ[volume] fun ξ => phase h ξ * v ξ := by
  have hb := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    (r := 2) ((phase_memLp_top h).toLp (phase h)) v
  filter_upwards [hb, (phase_memLp_top h).coeFn_toLp] with ξ hbξ hpξ
  simpa [modulateL2, ContinuousLinearMap.holderL_apply_apply, hpξ] using hbξ

theorem translateL2_schwartz (h : FourSpace) (f : 𝓢(FourSpace, ℂ)) :
    translateL2 h (f.toLp 2) = (f.compSubConstCLM ℂ (-h)).toLp 2 := by
  apply Lp.ext
  have hc := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae
    (f.coeFn_toLp 2 volume)
  filter_upwards [translateL2_ae h (f.toLp 2), hc,
    (f.compSubConstCLM ℂ (-h)).coeFn_toLp 2] with x hx hcx hfx
  simpa [hfx, hcx, SchwartzMap.compSubConstCLM_apply] using hx

theorem fourier_translate_schwartz (h : FourSpace) (f : 𝓢(FourSpace, ℂ)) (ξ : FourSpace) :
    𝓕 (f.compSubConstCLM ℂ (-h)) ξ = phase h ξ * 𝓕 f ξ := by
  have hh := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ FourSpace) (f : FourSpace → ℂ) h) ξ
  change 𝓕 ((f.compSubConstCLM ℂ (-h)) : FourSpace → ℂ) ξ =
    phase h ξ * 𝓕 (f : FourSpace → ℂ) ξ
  have hc : ((f.compSubConstCLM ℂ (-h)) : FourSpace → ℂ) =
      (f : FourSpace → ℂ) ∘ (fun x => x + h) := by
    ext x
    simp [SchwartzMap.compSubConstCLM_apply]
  rw [hc]
  exact hh

/-- Fourier translation for all L2 functions, obtained by extending the
actual Schwartz translation identity along its dense L2 image. -/
theorem fourier_translateL2 (h : FourSpace) (v : LocalL2) :
    𝓕 (translateL2 h v) = modulateL2 h (𝓕 v) := by
  set p := fun v : LocalL2 => 𝓕 (translateL2 h v) = modulateL2 h (𝓕 v)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) v
  · apply isClosed_eq
    · exact ((fourierCLM ℂ LocalL2).comp (translateL2 h)).continuous
    · exact ((modulateL2 h).comp (fourierCLM ℂ LocalL2)).continuous
  intro f
  change 𝓕 (translateL2 h (f.toLp 2)) = modulateL2 h (𝓕 (f.toLp 2))
  rw [translateL2_schwartz, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (f.compSubConstCLM ℂ (-h))).coeFn_toLp 2,
    modulateL2_ae h ((𝓕 f).toLp 2), (𝓕 f).coeFn_toLp 2] with ξ hx hy hz
  rw [hx, hy, hz]
  exact fourier_translate_schwartz h f ξ


end K24.Global.SobolevFractional
end K24SOBFRACTIONAL_Translation_Bundle


/- Inlined source K24SOBFRACTIONAL_Energy.lean; SHA256 a3c5336f536efdb8008741c0308b727cbffca7d39f8131044af32932e172ad4a. -/
noncomputable section K24SOBFRACTIONAL_Energy_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 16
open MeasureTheory FourierTransform Filter
open scoped ENNReal NNReal SchwartzMap Topology

namespace K24.Global.SobolevFractional

theorem eLpNorm_two_sq (f : FourSpace → ℂ) :
    (eLpNorm f 2 volume) ^ (2 : ℕ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) := by
  simpa only [NNReal.coe_ofNat, ENNReal.rpow_two, ENNReal.coe_ofNat] using
    (eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := volume)
      (by norm_num : (2 : ℝ≥0) ≠ 0))

theorem fourier_difference_ae (h : FourSpace) (v : LocalL2) :
    (𝓕 (translateL2 h v - v) : LocalL2) =ᵐ[volume]
      fun ξ => (phase h ξ - 1) * (𝓕 v) ξ := by
  have he : 𝓕 (translateL2 h v - v) = modulateL2 h (𝓕 v) - 𝓕 v := by
    change (fourierCLM ℂ LocalL2) (translateL2 h v - v) = _
    rw [map_sub]
    change 𝓕 (translateL2 h v) - 𝓕 v = _
    rw [fourier_translateL2]
  rw [he]
  filter_upwards [Lp.coeFn_sub (modulateL2 h (𝓕 v)) (𝓕 v),
    modulateL2_ae h (𝓕 v)] with ξ hs hm
  simp only [hs, hm, Pi.sub_apply]
  ring

/-- Plancherel for an actual fixed spatial difference, not an assumed
fractional identity. -/
theorem difference_plancherel (h : FourSpace) (v : LocalL2) :
    (∫⁻ x, ‖v (x + h) - v x‖ₑ ^ (2 : ℕ)) =
      ∫⁻ ξ, ‖phase h ξ - 1‖ₑ ^ (2 : ℕ) * ‖(𝓕 v) ξ‖ₑ ^ (2 : ℕ) := by
  have ha : translateL2 h v - v =ᵐ[volume] fun x => v (x + h) - v x := by
    filter_upwards [Lp.coeFn_sub (translateL2 h v) v, translateL2_ae h v]
      with x hs ht
    simpa only [Pi.sub_apply, ht] using hs
  have hn : eLpNorm (fun x => v (x + h) - v x) 2 volume =
      eLpNorm (fun ξ => (phase h ξ - 1) * (𝓕 v) ξ) 2 volume := by
    rw [← eLpNorm_congr_ae ha, ← eLpNorm_congr_ae (fourier_difference_ae h v),
      ← Lp.enorm_def, ← Lp.enorm_def, ← ofReal_norm, ← ofReal_norm,
      Lp.norm_fourier_eq]
  rw [← eLpNorm_two_sq, hn, eLpNorm_two_sq]
  simp only [enorm_mul, mul_pow]

theorem ofReal_norm_sq (z : ℂ) : ENNReal.ofReal (‖z‖ ^ (2 : ℕ)) = ‖z‖ₑ ^ (2 : ℕ) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

def fractionalWeight (α : ℝ) (h : FourSpace) : ℝ≥0∞ :=
  ENNReal.ofReal ((‖h‖ ^ ((4 : ℝ) + 2 * α))⁻¹)

theorem measurable_fractionalWeight (α : ℝ) : Measurable (fractionalWeight α) := by
  unfold fractionalWeight
  fun_prop

theorem quotient_norm_sq (α : ℝ) (h : FourSpace) (z : ℂ) :
    ENNReal.ofReal (‖z‖ ^ (2 : ℕ) / ‖h‖ ^ ((4 : ℝ) + 2 * α)) =
      ‖z‖ₑ ^ (2 : ℕ) * fractionalWeight α h := by
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (sq_nonneg _), ofReal_norm_sq]
  rfl

/-- Translation-variable fractional energy equals its actual Fourier kernel
integral. The identity holds with extended values, including infinite energy.
No regularity beyond membership of the genuine L2 class is imposed. -/
theorem fractional_energy_fourier_raw (α : ℝ) (v : LocalL2) :
    (∫⁻ h : FourSpace, ∫⁻ x : FourSpace,
      ENNReal.ofReal (‖v (x + h) - v x‖ ^ (2 : ℕ) /
        ‖h‖ ^ ((4 : ℝ) + 2 * α))) =
    ∫⁻ ξ : FourSpace, ‖(𝓕 v) ξ‖ₑ ^ (2 : ℕ) *
      ∫⁻ h : FourSpace, ENNReal.ofReal (‖phase h ξ - 1‖ ^ (2 : ℕ) /
        ‖h‖ ^ ((4 : ℝ) + 2 * α)) := by
  simp_rw [quotient_norm_sq]
  have hp : Measurable (fun z : FourSpace × FourSpace => phase z.1 z.2) := by
    exact ((continuous_subtype_val.comp Real.continuous_fourierChar).comp
      (by fun_prop)).measurable
  have hm : AEMeasurable (fun z : FourSpace × FourSpace =>
      (‖phase z.1 z.2 - 1‖ₑ ^ (2 : ℕ) * ‖(𝓕 v) z.2‖ₑ ^ (2 : ℕ)) *
        fractionalWeight α z.1) (volume.prod volume) :=
    (((hp.sub measurable_const).enorm.pow_const 2).aemeasurable.mul
      ((Lp.aestronglyMeasurable (𝓕 v)).enorm.pow_const 2).comp_snd).mul
        ((measurable_fractionalWeight α).comp measurable_fst).aemeasurable
  calc
    _ = ∫⁻ h : FourSpace,
        (∫⁻ x : FourSpace, ‖v (x + h) - v x‖ₑ ^ (2 : ℕ)) * fractionalWeight α h := by
      apply lintegral_congr
      intro h
      exact lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ = ∫⁻ h : FourSpace,
        (∫⁻ ξ : FourSpace, ‖phase h ξ - 1‖ₑ ^ (2 : ℕ) * ‖(𝓕 v) ξ‖ₑ ^ (2 : ℕ)) *
          fractionalWeight α h := by simp_rw [difference_plancherel]
    _ = ∫⁻ h : FourSpace, ∫⁻ ξ : FourSpace,
        (‖phase h ξ - 1‖ₑ ^ (2 : ℕ) * ‖(𝓕 v) ξ‖ₑ ^ (2 : ℕ)) *
          fractionalWeight α h := by
      apply lintegral_congr
      intro h
      exact (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ ξ : FourSpace, ∫⁻ h : FourSpace,
        (‖phase h ξ - 1‖ₑ ^ (2 : ℕ) * ‖(𝓕 v) ξ‖ₑ ^ (2 : ℕ)) *
          fractionalWeight α h := lintegral_lintegral_swap hm
    _ = _ := by
      apply lintegral_congr
      intro ξ
      simp_rw [mul_right_comm (‖phase _ ξ - 1‖ₑ ^ (2 : ℕ)),
        mul_comm _ (‖(𝓕 v) ξ‖ₑ ^ (2 : ℕ))]
      exact lintegral_const_mul' _ _ (by finiteness)


end K24.Global.SobolevFractional
end K24SOBFRACTIONAL_Energy_Bundle


/- Inlined source K24SOBFRACTIONAL_Identity.lean; SHA256 1173604879e9d00fe896e7da764ca4e1e3ac27a1f1abeb89646b204d328a27c1. -/
noncomputable section K24SOBFRACTIONAL_Identity_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 16
open MeasureTheory FourierTransform Filter Set
open scoped ENNReal NNReal SchwartzMap Topology

namespace K24.Global.SobolevFractional
open SobolevComposition

/-- The original two-point energy is exactly the translation-variable energy.
Joint measurability is derived from the actual measurable representative and
the Haar-measure-preserving addition map. -/
theorem fractionalDifferenceEnergy_eq_translation (α : ℝ) (f : FourSpace → ℂ)
    (hf : AEStronglyMeasurable f volume) :
    fractionalDifferenceEnergy α univ f =
      ∫⁻ h : FourSpace, ∫⁻ x : FourSpace,
        ENNReal.ofReal (‖f (x + h) - f x‖ ^ (2 : ℕ) /
          ‖h‖ ^ ((4 : ℝ) + 2 * α)) := by
  have ha := hf.aemeasurable.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_add volume volume)
  have hm : AEMeasurable (fun z : FourSpace × FourSpace =>
      ENNReal.ofReal (‖f (z.1 + z.2) - f z.1‖ ^ (2 : ℕ) /
        ‖z.2‖ ^ ((4 : ℝ) + 2 * α))) (volume.prod volume) := by
    exact (((ha.sub hf.aemeasurable.comp_fst).norm.pow_const 2).div
      (by fun_prop)).ennreal_ofReal
  simp only [fractionalDifferenceEnergy, Measure.restrict_univ]
  calc
    _ = ∫⁻ x : FourSpace, ∫⁻ h : FourSpace,
        ENNReal.ofReal (‖f (x + h) - f x‖ ^ (2 : ℕ) /
          ‖h‖ ^ ((4 : ℝ) + 2 * α)) := by
      apply lintegral_congr
      intro x
      rw [← lintegral_add_left_eq_self
        (fun y => ENNReal.ofReal (‖f x - f y‖ ^ (2 : ℕ) /
          ‖x - y‖ ^ ((4 : ℝ) + 2 * α))) x]
      apply lintegral_congr
      intro h
      rw [norm_sub_rev (f x)]
      simp only [sub_add_cancel_left, norm_neg]
    _ = _ := lintegral_lintegral_swap hm

/-- Exact fractional Plancherel identity in the existing composition energy
and Fourier-kernel definitions. It is valid for every real exponent as an
extended-valued identity; the meaningful finite-kernel range is 0 < α < 1. -/
theorem fractionalDifferenceEnergy_fourier (α : ℝ) (v : LocalL2) :
    fractionalDifferenceEnergy α univ v =
      ∫⁻ ξ : FourSpace, ‖(𝓕 v) ξ‖ₑ ^ (2 : ℕ) * fractionalFourierKernel α ξ := by
  rw [fractionalDifferenceEnergy_eq_translation α _ (Lp.aestronglyMeasurable v)]
  exact fractional_energy_fourier_raw α v

/-- The same identity for an arbitrary given MemLp representative. The
spatial energy is computed from f itself, not from the selected Lp version. -/
theorem fractionalDifferenceEnergy_fourier_memLp (α : ℝ) (f : FourSpace → ℂ)
    (hf : MemLp f 2 volume) :
    fractionalDifferenceEnergy α univ f =
      ∫⁻ ξ : FourSpace, ‖(𝓕 (hf.toLp f) : LocalL2) ξ‖ₑ ^ (2 : ℕ) *
        fractionalFourierKernel α ξ := by
  rw [fractionalDifferenceEnergy_eq_translation α f hf.1,
    ← fractionalDifferenceEnergy_fourier,
    fractionalDifferenceEnergy_eq_translation α _ (Lp.aestronglyMeasurable (hf.toLp f))]
  apply lintegral_congr
  intro h
  apply lintegral_congr_ae
  have ht := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae hf.coeFn_toLp
  filter_upwards [hf.coeFn_toLp, ht] with x hx htx
  rw [hx, htx]


end K24.Global.SobolevFractional
end K24SOBFRACTIONAL_Identity_Bundle


/- Inlined source K24SOBCOMPOSE_PullbackEnergy.lean; SHA256 d7234de71a500f92596ec7e36ed105ba6e38a5645b51a5d0b424ec1792749577. -/
noncomputable section K24SOBCOMPOSE_PullbackEnergy_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace K24.Global.SobolevComposition

/-- Global nonlinear pullback controls the genuine squared L2 norm by its
actual reciprocal-Jacobian bound, without assuming measure domination. -/
theorem eLpNorm_comp_sq_le
    (φ : FourSpace → FourSpace) (Dφ : FourSpace → FourSpace →L[ℝ] FourSpace)
    (hd : ∀ x, HasFDerivAt φ (Dφ x) x) (hi : Function.Injective φ)
    (J : ℝ≥0) (hJ : ∀ x, (1 : ℝ≥0∞) ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(Dφ x).det|)
    (f : FourSpace → ℂ) :
    (eLpNorm (f ∘ φ) 2 volume)^2 ≤ (J : ℝ≥0∞) * (eLpNorm f 2 volume)^2 := by
  rw [SobolevFractional.eLpNorm_two_sq, SobolevFractional.eLpNorm_two_sq]
  have h := lintegral_comp_le_of_jacobian univ MeasurableSet.univ φ Dφ
    (fun x _ => (hd x).hasFDerivWithinAt) hi.injOn J (fun x _ => hJ x)
    (fun x => ‖f x‖ₑ ^ (2 : ℕ))
  simp only [Measure.restrict_univ] at h
  exact h.trans (mul_le_mul (le_refl _) (lintegral_mono' Measure.restrict_le_self (le_refl _)) bot_le bot_le)

theorem memLp_comp_of_jacobian
    (φ : FourSpace → FourSpace) (Dφ : FourSpace → FourSpace →L[ℝ] FourSpace)
    (hd : ∀ x, HasFDerivAt φ (Dφ x) x) (hi : Function.Injective φ)
    (J : ℝ≥0) (hJ : ∀ x, (1 : ℝ≥0∞) ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(Dφ x).det|)
    (f : FourSpace → ℂ) (hf : Continuous f) (hf2 : MemLp f 2 volume) :
    MemLp (f ∘ φ) 2 volume := by
  have hc : Continuous φ := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  refine ⟨(hf.comp hc).aestronglyMeasurable, ?_⟩
  have hs : (eLpNorm (f ∘ φ) 2 volume)^2 < ⊤ :=
    (eLpNorm_comp_sq_le φ Dφ hd hi J hJ f).trans_lt
      (ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.pow_lt_top hf2.eLpNorm_lt_top))
  simpa only [ENNReal.pow_lt_top_iff, OfNat.ofNat_ne_zero, or_false] using hs

/-- The full-space energy estimate remains genuinely nonlinear: φ is an
arbitrary differentiable injective map with its displayed actual bounds. -/
theorem fractionalDifferenceEnergy_comp_univ_le
    (α : ℝ) (hα : 0 < α)
    (φ : FourSpace → FourSpace) (Dφ : FourSpace → FourSpace →L[ℝ] FourSpace)
    (hd : ∀ x, HasFDerivAt φ (Dφ x) x) (hi : Function.Injective φ)
    (J L : ℝ≥0)
    (hJ : ∀ x, (1 : ℝ≥0∞) ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(Dφ x).det|)
    (hL : ∀ x y, ‖φ x-φ y‖ ≤ (L : ℝ) * ‖x-y‖)
    (f : FourSpace → ℂ) :
    fractionalDifferenceEnergy α univ (f ∘ φ) ≤
      ENNReal.ofReal ((L : ℝ) ^ ((4 : ℝ)+2*α)) * (J : ℝ≥0∞)^2 *
        fractionalDifferenceEnergy α univ f := by
  apply (fractionalDifferenceEnergy_comp_le α hα univ MeasurableSet.univ φ Dφ
    (fun x _ => (hd x).hasFDerivWithinAt) hi.injOn J L
    (fun x _ => hJ x) (fun x _ y _ => hL x y) f).trans
  apply mul_le_mul (le_refl _) _ bot_le bot_le
  unfold fractionalDifferenceEnergy
  simp only [Measure.restrict_univ]
  calc
    _ ≤ ∫⁻ x in φ '' univ, ∫⁻ y,
        ENNReal.ofReal (‖f x-f y‖^2 / ‖x-y‖^((4:ℝ)+2*α)) :=
      lintegral_mono (fun _ => lintegral_mono' Measure.restrict_le_self (le_refl _))
    _ ≤ _ := lintegral_mono' Measure.restrict_le_self (le_refl _)

end K24.Global.SobolevComposition
end K24SOBCOMPOSE_PullbackEnergy_Bundle


/- Inlined source K24SOBAECOMP_QuasiMeasure.lean; SHA256 447272beea6598803cd9bc74738159a1716450dd4d2a45b160424342522ebafc. -/
noncomputable section K24SOBAECOMP_QuasiMeasure_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace K24.Global.SobolevComposition

/-- The actual Jacobian formula gives full-space integral domination for
arbitrary nonnegative integrands, without a measurability premise on them. -/
theorem lintegral_comp_univ_le_of_jacobian
    (φ : FourSpace → FourSpace) (Dφ : FourSpace → FourSpace →L[ℝ] FourSpace)
    (hd : ∀ x, HasFDerivAt φ (Dφ x) x) (hi : Function.Injective φ)
    (J : ℝ≥0)
    (hJ : ∀ x, (1 : ℝ≥0∞) ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(Dφ x).det|)
    (g : FourSpace → ℝ≥0∞) :
    (∫⁻ x, g (φ x)) ≤ (J : ℝ≥0∞) * ∫⁻ x, g x := by
  have h := lintegral_comp_le_of_jacobian univ MeasurableSet.univ φ Dφ
    (fun x _ => (hd x).hasFDerivWithinAt) hi.injOn J (fun x _ => hJ x) g
  simp only [Measure.restrict_univ] at h
  exact h.trans (mul_le_mul (le_refl _)
    (lintegral_mono' Measure.restrict_le_self (le_refl _)) bot_le bot_le)

/-- Pullback of volume is dominated by the genuine reciprocal-Jacobian
constant. This is derived on measurable indicators from change of variables. -/
theorem map_volume_le_of_jacobian
    (φ : FourSpace → FourSpace) (Dφ : FourSpace → FourSpace →L[ℝ] FourSpace)
    (hd : ∀ x, HasFDerivAt φ (Dφ x) x) (hi : Function.Injective φ)
    (J : ℝ≥0)
    (hJ : ∀ x, (1 : ℝ≥0∞) ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(Dφ x).det|) :
    Measure.map φ volume ≤ (J : ℝ≥0∞) • (volume : Measure FourSpace) := by
  have hφ : Measurable φ :=
    (continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)).measurable
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.smul_apply, smul_eq_mul]
  calc
    (Measure.map φ volume) s =
        ∫⁻ x, s.indicator (fun _ => (1 : ℝ≥0∞)) (φ x) := by
      rw [← lintegral_indicator_one hs]
      exact lintegral_map (measurable_const.indicator hs) hφ
    _ ≤ (J : ℝ≥0∞) * ∫⁻ x, s.indicator (fun _ => (1 : ℝ≥0∞)) x :=
      lintegral_comp_univ_le_of_jacobian φ Dφ hd hi J hJ _
    _ = _ := by rw [lintegral_indicator_const hs]; simp

/-- Nonsingularity of the actual coordinate map follows from its proved
Jacobian domination. Thus arbitrary null-set modifications remain null after
composition; no representative regularity is assumed. -/
theorem quasiMeasurePreserving_of_jacobian
    (φ : FourSpace → FourSpace) (Dφ : FourSpace → FourSpace →L[ℝ] FourSpace)
    (hd : ∀ x, HasFDerivAt φ (Dφ x) x) (hi : Function.Injective φ)
    (J : ℝ≥0)
    (hJ : ∀ x, (1 : ℝ≥0∞) ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(Dφ x).det|) :
    Measure.QuasiMeasurePreserving φ volume volume := by
  refine ⟨(continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)).measurable, ?_⟩
  exact Measure.absolutelyContinuous_of_le_smul
    (map_volume_le_of_jacobian φ Dφ hd hi J hJ)

/-- The standard arbitrary representatives of L2 functions pull back to
actual L2 functions: measurability is transported by the proved nonsingularity. -/
theorem memLp_comp_of_jacobian_ae
    (φ : FourSpace → FourSpace) (Dφ : FourSpace → FourSpace →L[ℝ] FourSpace)
    (hd : ∀ x, HasFDerivAt φ (Dφ x) x) (hi : Function.Injective φ)
    (J : ℝ≥0)
    (hJ : ∀ x, (1 : ℝ≥0∞) ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(Dφ x).det|)
    (f : FourSpace → ℂ) (hf : MemLp f 2 volume) :
    MemLp (f ∘ φ) 2 volume := by
  have hφ := quasiMeasurePreserving_of_jacobian φ Dφ hd hi J hJ
  refine ⟨hf.aestronglyMeasurable.comp_quasiMeasurePreserving hφ, ?_⟩
  have hs : (eLpNorm (f ∘ φ) 2 volume)^2 < ⊤ :=
    (eLpNorm_comp_sq_le φ Dφ hd hi J hJ f).trans_lt
      (ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.pow_lt_top hf.eLpNorm_lt_top))
  simpa only [ENNReal.pow_lt_top_iff, OfNat.ofNat_ne_zero, or_false] using hs

/-- Equality almost everywhere is respected by the actual composition,
independently of any continuity or differentiability of the coefficients. -/
theorem ae_eq_comp_of_jacobian {E : Type*}
    (φ : FourSpace → FourSpace) (Dφ : FourSpace → FourSpace →L[ℝ] FourSpace)
    (hd : ∀ x, HasFDerivAt φ (Dφ x) x) (hi : Function.Injective φ)
    (J : ℝ≥0)
    (hJ : ∀ x, (1 : ℝ≥0∞) ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(Dφ x).det|)
    {f g : FourSpace → E} (hfg : f =ᵐ[volume] g) :
    f ∘ φ =ᵐ[volume] g ∘ φ :=
  (quasiMeasurePreserving_of_jacobian φ Dφ hd hi J hJ).ae_eq hfg

end K24.Global.SobolevComposition

end K24SOBAECOMP_QuasiMeasure_Bundle


/- Inlined source K24SOBFRACTIONAL_Bessel.lean; SHA256 80639d86ed4d421c5e6d5dad3b02e93ccdef04c29619428b50028fbc31e30efd. -/
noncomputable section K24SOBFRACTIONAL_Bessel_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 16
open MeasureTheory FourierTransform TemperedDistribution Filter
open scoped ENNReal NNReal SchwartzMap Topology

namespace K24.Global.SobolevFractional

def besselFourierWeight (s : ℝ) (ξ : FourSpace) : ℂ :=
  ((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ)

theorem besselFourierWeight_temperate (s : ℝ) :
    (besselFourierWeight s).HasTemperateGrowth := by
  unfold besselFourierWeight
  fun_prop

theorem besselFourierWeight_neg_mul (s : ℝ) (ξ : FourSpace) :
    besselFourierWeight s ξ * besselFourierWeight (-s) ξ = 1 := by
  unfold besselFourierWeight
  norm_cast
  rw [← Real.rpow_add (by positivity)]
  ring_nf
  simp

theorem besselFourierWeight_neg_top {s : ℝ} (hs : 0 ≤ s) :
    MemLp (besselFourierWeight (-s)) ∞ volume := by
  apply memLp_top_of_bound (besselFourierWeight_temperate (-s)).1.continuous.aestronglyMeasurable 1
  apply ae_of_all
  intro ξ
  change ‖(((1 + ‖ξ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖ξ‖]) (by linarith)

/-- Finite exact weighted L2 norm constructs the original Bessel potential
representative, with equality of the canonical extended norm. -/
theorem bessel_norm_of_weighted {s : ℝ} (v : LocalL2)
    (hw : MemLp (fun ξ => besselFourierWeight s ξ * (𝓕 v) ξ) 2 volume) :
    BesselMem s (v : LocalDistribution) ∧
      besselSobolevENN s (v : LocalDistribution) =
        eLpNorm (fun ξ => besselFourierWeight s ξ * (𝓕 v) ξ) 2 volume := by
  let w : LocalL2 := hw.toLp (fun ξ => besselFourierWeight s ξ * (𝓕 v) ξ)
  have hwT : smulLeftCLM ℂ (besselFourierWeight s) ((𝓕 v : LocalL2) : LocalDistribution) =
      (w : LocalDistribution) := by
    ext φ
    rw [smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
      Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [hw.coeFn_toLp] with ξ hξ
    simp only [w, hξ, SchwartzMap.smulLeftCLM_apply_apply
      (besselFourierWeight_temperate s), smul_eq_mul]
    ring
  have hrep : besselPotential FourSpace ℂ s (v : LocalDistribution) =
      ((𝓕⁻ w : LocalL2) : LocalDistribution) := by
    rw [besselPotential, TemperedDistribution.fourierMultiplierCLM_apply,
      Lp.fourier_toTemperedDistribution_eq]
    change 𝓕⁻ (smulLeftCLM ℂ (besselFourierWeight s)
      ((𝓕 v : LocalL2) : LocalDistribution)) = _
    rw [hwT, Lp.fourierInv_toTemperedDistribution_eq]
  refine ⟨⟨𝓕⁻ w, hrep⟩, ?_⟩
  have hnorm : ‖𝓕⁻ w‖ = ‖w‖ := by
    rw [← Lp.norm_fourier_eq (𝓕⁻ w), fourier_fourierInv_eq]
  rw [besselSobolevENN_eq_of_rep _ hrep, hnorm, ofReal_norm]
  exact Lp.enorm_toLp hw

/-- For nonnegative real order, the original Bessel assumption forces the
actual Fourier representative to have finite weighted L2 norm. The inverse
weight is genuinely bounded and the distribution identity determines the L2
representative uniquely. -/
theorem weighted_memLp_of_bessel {s : ℝ} (hs : 0 ≤ s) (v : LocalL2)
    (hv : BesselMem s (v : LocalDistribution)) :
    MemLp (fun ξ => besselFourierWeight s ξ * (𝓕 v) ξ) 2 volume := by
  let u : LocalL2 := 𝓕 (besselRepresentative hv)
  have hu : smulLeftCLM ℂ (besselFourierWeight s) (𝓕 (v : LocalDistribution)) =
      (u : LocalDistribution) := by
    change smulLeftCLM ℂ (fun ξ : FourSpace =>
      (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) (𝓕 (v : LocalDistribution)) = _
    rw [← fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
      besselRepresentative_spec hv, Lp.fourier_toTemperedDistribution_eq]
  let hd := besselFourierWeight_neg_top hs
  let v' : LocalL2 := hd.toLp (besselFourierWeight (-s)) • u
  have hv'T : (v' : LocalDistribution) = 𝓕 (v : LocalDistribution) := by
    dsimp [v']
    rw [Lp.toTemperedDistribution_smul_eq (besselFourierWeight_temperate (-s))]
    rw [← hu, smulLeftCLM_smulLeftCLM_apply
      (besselFourierWeight_temperate s) (besselFourierWeight_temperate (-s))]
    have he : besselFourierWeight s * besselFourierWeight (-s) = fun _ => (1 : ℂ) := by
      ext ξ
      exact besselFourierWeight_neg_mul s ξ
    rw [he]
    simp
  have hv'eq : v' = 𝓕 v := by
    apply localL2_distribution_injective
    exact hv'T.trans (Lp.fourier_toTemperedDistribution_eq v)
  have hpoint : (𝓕 v : LocalL2) =ᵐ[volume]
      fun ξ => besselFourierWeight (-s) ξ * u ξ := by
    rw [← hv'eq]
    filter_upwards [Lp.coeFn_lpSMul (r := 2) (hd.toLp (besselFourierWeight (-s))) u,
      hd.coeFn_toLp] with ξ hξ hdξ
    simpa only [v', Pi.smul_apply', smul_eq_mul, hdξ] using hξ
  have hw : (fun ξ => besselFourierWeight s ξ * (𝓕 v) ξ) =ᵐ[volume] u := by
    filter_upwards [hpoint] with ξ hξ
    rw [hξ, ← mul_assoc, besselFourierWeight_neg_mul, one_mul]
  exact (Lp.memLp u).ae_eq hw.symm

theorem besselMem_iff_weighted_memLp {s : ℝ} (hs : 0 ≤ s) (v : LocalL2) :
    BesselMem s (v : LocalDistribution) ↔
      MemLp (fun ξ => besselFourierWeight s ξ * (𝓕 v) ξ) 2 volume :=
  ⟨weighted_memLp_of_bessel hs v, fun h => (bessel_norm_of_weighted v h).1⟩

/-- Exact original Bessel norm as a weighted Fourier L2 norm, including
infinite values; this is an identity, not a replacement norm definition. -/
theorem besselSobolevENN_eq_weighted {s : ℝ} (hs : 0 ≤ s) (v : LocalL2) :
    besselSobolevENN s (v : LocalDistribution) =
      eLpNorm (fun ξ => besselFourierWeight s ξ * (𝓕 v) ξ) 2 volume := by
  by_cases hw : MemLp (fun ξ => besselFourierWeight s ξ * (𝓕 v) ξ) 2 volume
  · exact (bessel_norm_of_weighted v hw).2
  have hb : ¬ BesselMem s (v : LocalDistribution) :=
    fun hb => hw (weighted_memLp_of_bessel hs v hb)
  rw [besselSobolevENN, dif_neg hb]
  apply Eq.symm
  apply top_unique
  by_contra hn
  apply hw
  refine ⟨(besselFourierWeight_temperate s).1.continuous.aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable (𝓕 v)), ?_⟩
  exact lt_of_not_ge hn


end K24.Global.SobolevFractional
end K24SOBFRACTIONAL_Bessel_Bundle


/- Inlined source K24SOBFRACTIONAL_Comparison.lean; SHA256 c8583b2f037c7d0adf28765908d4981202af1b953c1622168220f5cddd6180cd. -/
noncomputable section K24SOBFRACTIONAL_Comparison_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 16
open MeasureTheory FourierTransform Filter Set
open scoped ENNReal NNReal SchwartzMap Topology

namespace K24.Global.SobolevFractional
open SobolevComposition

def spectralMoment (α : ℝ) (v : LocalL2) : ℝ≥0∞ :=
  ∫⁻ ξ : FourSpace, ENNReal.ofReal (‖ξ‖ ^ (2 * α)) * ‖(𝓕 v) ξ‖ₑ ^ (2 : ℕ)

theorem besselSobolevENN_sq_integral {s : ℝ} (hs : 0 ≤ s) (v : LocalL2) :
    besselSobolevENN s (v : LocalDistribution) ^ (2 : ℕ) =
      ∫⁻ ξ : FourSpace, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s) *
        ‖(𝓕 v) ξ‖ₑ ^ (2 : ℕ) := by
  rw [besselSobolevENN_eq_weighted hs, eLpNorm_two_sq]
  apply lintegral_congr
  intro ξ
  rw [enorm_mul, mul_pow]
  congr 1
  rw [← ofReal_norm_sq]
  congr 1
  simp only [besselFourierWeight, Complex.norm_real, Real.norm_eq_abs]
  rw [sq_abs, ← Real.rpow_mul_natCast (by positivity)]
  congr 1
  norm_num

theorem norm_sq_fourier_integral (v : LocalL2) :
    ‖v‖ₑ ^ (2 : ℕ) = ∫⁻ ξ : FourSpace, ‖(𝓕 v) ξ‖ₑ ^ (2 : ℕ) := by
  rw [← eLpNorm_two_sq, ← Lp.enorm_def]
  simp only [← ofReal_norm, Lp.norm_fourier_eq]

theorem bessel_weight_split {s : ℝ} (hs : 0 ≤ s) (ξ : FourSpace) :
    (1 + ‖ξ‖ ^ 2) ^ s ≤ (2 : ℝ) ^ s * (1 + ‖ξ‖ ^ (2 * s)) := by
  have hpow : (‖ξ‖ ^ (2 : ℕ)) ^ s = ‖ξ‖ ^ (2 * s) :=
    (Real.rpow_natCast_mul (norm_nonneg ξ) 2 s).symm
  by_cases hξ : ‖ξ‖ ≤ 1
  · have hh : 1 + ‖ξ‖ ^ 2 ≤ 2 := by nlinarith [norm_nonneg ξ]
    calc
      _ ≤ (2 : ℝ) ^ s := Real.rpow_le_rpow (by positivity) hh hs
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (by positivity))
  · have hξ : 1 ≤ ‖ξ‖ := (lt_of_not_ge hξ).le
    have hh : 1 + ‖ξ‖ ^ 2 ≤ 2 * ‖ξ‖ ^ 2 := by nlinarith
    calc
      _ ≤ (2 * ‖ξ‖ ^ 2) ^ s := Real.rpow_le_rpow (by positivity) hh hs
      _ = (2 : ℝ) ^ s * ‖ξ‖ ^ (2 * s) := by rw [Real.mul_rpow (by positivity) (by positivity), hpow]
      _ ≤ _ := by gcongr; linarith

theorem norm_sq_le_bessel_sq {s : ℝ} (hs : 0 ≤ s) (v : LocalL2) :
    ‖v‖ₑ ^ (2 : ℕ) ≤ besselSobolevENN s (v : LocalDistribution) ^ (2 : ℕ) := by
  rw [norm_sq_fourier_integral, besselSobolevENN_sq_integral hs]
  apply lintegral_mono
  intro ξ
  have hw : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
      (Real.one_le_rpow (show 1 ≤ 1 + ‖ξ‖ ^ 2 by nlinarith [sq_nonneg ‖ξ‖]) hs)
  simpa using mul_le_mul_left hw (‖(𝓕 v) ξ‖ₑ ^ (2 : ℕ))

theorem spectralMoment_le_bessel_sq {s : ℝ} (hs : 0 ≤ s) (v : LocalL2) :
    spectralMoment s v ≤ besselSobolevENN s (v : LocalDistribution) ^ (2 : ℕ) := by
  rw [spectralMoment, besselSobolevENN_sq_integral hs]
  apply lintegral_mono
  intro ξ
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  have he : ‖ξ‖ ^ (2 * s) = (‖ξ‖ ^ (2 : ℕ)) ^ s := by
    simpa only [Nat.cast_ofNat] using Real.rpow_natCast_mul (norm_nonneg ξ) 2 s
  rw [he]
  exact Real.rpow_le_rpow (by positivity) (by linarith) hs

theorem bessel_sq_le_norm_sq_add_moment {s : ℝ} (hs : 0 ≤ s) (v : LocalL2) :
    besselSobolevENN s (v : LocalDistribution) ^ (2 : ℕ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ s) * (‖v‖ₑ ^ (2 : ℕ) + spectralMoment s v) := by
  rw [besselSobolevENN_sq_integral hs]
  calc
    _ ≤ ∫⁻ ξ : FourSpace, ENNReal.ofReal ((2 : ℝ) ^ s) *
        (1 + ENNReal.ofReal (‖ξ‖ ^ (2 * s))) * ‖(𝓕 v) ξ‖ₑ ^ (2 : ℕ) := by
      apply lintegral_mono
      intro ξ
      apply mul_le_mul_left
      simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ s),
        ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
          (by positivity : 0 ≤ ‖ξ‖ ^ (2 * s)), ENNReal.ofReal_one]
        using ENNReal.ofReal_le_ofReal (bessel_weight_split hs ξ)
    _ = _ := by
      simp_rw [mul_assoc, add_mul, one_mul]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left' ((Lp.aestronglyMeasurable (𝓕 v)).enorm.pow_const 2),
        ← norm_sq_fourier_integral]
      rfl

theorem energy_eq_constant_moment (α : ℝ) (c : ℝ≥0)
    (hc : ∀ ξ : FourSpace, fractionalFourierKernel α ξ =
      (c : ℝ≥0∞) * ENNReal.ofReal (‖ξ‖ ^ (2 * α))) (v : LocalL2) :
    fractionalDifferenceEnergy α univ v = (c : ℝ≥0∞) * spectralMoment α v := by
  rw [fractionalDifferenceEnergy_fourier]
  simp_rw [hc, mul_comm (‖(𝓕 v) _‖ₑ ^ (2 : ℕ)), mul_assoc]
  exact lintegral_const_mul' _ _ ENNReal.coe_ne_top

/-- Two quantitative comparisons with the unchanged canonical Bessel norm.
The constants are finite and depend only on the real fractional order. -/
theorem fractional_bessel_comparison (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ A B : ℝ≥0, 0 < A ∧ 0 < B ∧ ∀ v : LocalL2,
      besselSobolevENN α (v : LocalDistribution) ^ (2 : ℕ) ≤
        (A : ℝ≥0∞) * (‖v‖ₑ ^ (2 : ℕ) + fractionalDifferenceEnergy α univ v) ∧
      (‖v‖ₑ ^ (2 : ℕ) + fractionalDifferenceEnergy α univ v) ≤
        (B : ℝ≥0∞) * besselSobolevENN α (v : LocalDistribution) ^ (2 : ℕ) := by
  obtain ⟨c, hc, hkernel⟩ := fractionalFourierKernel_characterization α hα hα1
  let d : ℝ≥0 := Real.toNNReal ((2 : ℝ) ^ α)
  have hd : (d : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ α) := rfl
  have hdpos : 0 < d := Real.toNNReal_pos.mpr (by positivity)
  refine ⟨d * (1 + c⁻¹), 1 + c, mul_pos hdpos (by positivity), by positivity, ?_⟩
  intro v
  have he := energy_eq_constant_moment α c hkernel v
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  have hm : spectralMoment α v = (c : ℝ≥0∞)⁻¹ * fractionalDifferenceEnergy α univ v := by
    rw [he, ← mul_assoc, ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top, one_mul]
  constructor
  · calc
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ α) * (‖v‖ₑ ^ (2 : ℕ) + spectralMoment α v) :=
        bessel_sq_le_norm_sq_add_moment hα.le v
      _ = (d : ℝ≥0∞) * (‖v‖ₑ ^ (2 : ℕ) +
          (c : ℝ≥0∞)⁻¹ * fractionalDifferenceEnergy α univ v) := by rw [hm, hd]
      _ ≤ (d : ℝ≥0∞) * ((1 + (c : ℝ≥0∞)⁻¹) * ‖v‖ₑ ^ (2 : ℕ) +
          (1 + (c : ℝ≥0∞)⁻¹) * fractionalDifferenceEnergy α univ v) := by
        gcongr
        · exact le_mul_of_one_le_left' (le_self_add)
        · exact le_add_self
      _ = _ := by push_cast; rw [ENNReal.coe_inv hc.ne']; ring
  · rw [he]
    calc
      _ ≤ besselSobolevENN α (v : LocalDistribution) ^ (2 : ℕ) +
          (c : ℝ≥0∞) * besselSobolevENN α (v : LocalDistribution) ^ (2 : ℕ) :=
        add_le_add (norm_sq_le_bessel_sq hα.le v)
          (mul_le_mul_right (spectralMoment_le_bessel_sq hα.le v) _)
      _ = _ := by push_cast; ring

theorem besselMem_iff_fractional_energy (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (v : LocalL2) :
    BesselMem α (v : LocalDistribution) ↔ fractionalDifferenceEnergy α univ v < ⊤ := by
  obtain ⟨A, B, _, _, h⟩ := fractional_bessel_comparison α hα hα1
  constructor
  · intro hv
    have hn := (besselSobolevENN_lt_top_iff α (v : LocalDistribution)).mpr hv
    exact (le_add_left le_rfl).trans_lt ((h v).2.trans_lt (by finiteness))
  · intro he
    apply (besselSobolevENN_lt_top_iff α (v : LocalDistribution)).mp
    have hn : besselSobolevENN α (v : LocalDistribution) ^ (2 : ℕ) < ⊤ :=
      (h v).1.trans_lt (by finiteness)
    simpa only [ENNReal.pow_lt_top_iff, OfNat.ofNat_ne_zero, or_false] using hn


end K24.Global.SobolevFractional
end K24SOBFRACTIONAL_Comparison_Bundle


/- Inlined source K24SOBFRACTIONAL_Local.lean; SHA256 ba471cb7d3444f5f9ea52dd89be7ed1dfb75468766f8dbe55f9ed34850fbaa9b. -/
noncomputable section K24SOBFRACTIONAL_Local_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 16
open MeasureTheory FourierTransform Filter Set
open scoped ENNReal NNReal SchwartzMap Topology

namespace K24.Global.SobolevFractional
open SobolevComposition

theorem fractionalDifferenceEnergy_toLp (α : ℝ) (f : FourSpace → ℂ)
    (hf : MemLp f 2 volume) :
    fractionalDifferenceEnergy α univ (hf.toLp f) = fractionalDifferenceEnergy α univ f := by
  rw [fractionalDifferenceEnergy_fourier, fractionalDifferenceEnergy_fourier_memLp α f hf]

/-- Exact finite-energy characterization of the original local real-function
Bessel space at every fractional real order 0 < α < 1. -/
theorem localSobolevMem_iff_fractional_energy (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (f : FourSpace → ℝ) :
    LocalSobolevMem α f ↔ MemLp (complexifyLocal f) 2 volume ∧
      fractionalDifferenceEnergy α univ (complexifyLocal f) < ⊤ := by
  constructor
  · rintro ⟨hf, hB⟩
    refine ⟨hf, ?_⟩
    rw [← fractionalDifferenceEnergy_toLp α _ hf]
    exact (besselMem_iff_fractional_energy α hα hα1 (hf.toLp _)).mp hB
  · rintro ⟨hf, he⟩
    refine ⟨hf, ?_⟩
    apply (besselMem_iff_fractional_energy α hα hα1 (hf.toLp _)).mpr
    rwa [fractionalDifferenceEnergy_toLp]

/-- Both quantitative comparisons for the original local norm, evaluated on
the given function. No continuous representative or surrogate norm is used. -/
theorem localSobolev_fractional_comparison (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ A B : ℝ≥0, 0 < A ∧ 0 < B ∧ ∀ f : FourSpace → ℝ,
      ∀ hf : MemLp (complexifyLocal f) 2 volume,
      localSobolevENN α f ^ (2 : ℕ) ≤ (A : ℝ≥0∞) *
        (eLpNorm (complexifyLocal f) 2 volume ^ (2 : ℕ) +
          fractionalDifferenceEnergy α univ (complexifyLocal f)) ∧
      (eLpNorm (complexifyLocal f) 2 volume ^ (2 : ℕ) +
          fractionalDifferenceEnergy α univ (complexifyLocal f)) ≤
        (B : ℝ≥0∞) * localSobolevENN α f ^ (2 : ℕ) := by
  obtain ⟨A, B, hA, hB, h⟩ := fractional_bessel_comparison α hα hα1
  refine ⟨A, B, hA, hB, fun f hf => ?_⟩
  have hh := h (hf.toLp _)
  rw [fractionalDifferenceEnergy_toLp α _ hf, Lp.enorm_toLp hf] at hh
  simpa only [localSobolevENN, dif_pos hf, localFunctionDistribution] using hh


end K24.Global.SobolevFractional
end K24SOBFRACTIONAL_Local_Bundle


/- Inlined source K24SOBAECOMP_FractionalPullback.lean; SHA256 346e773947cd2313dce361aaf14e95a98beddc28b0f3afd481af3cc8cdd20355. -/
noncomputable section K24SOBAECOMP_FractionalPullback_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace K24.Global.SobolevComposition

/-- Nonlinear composition for every actual original fractional Sobolev
representative, including discontinuous and merely almost-everywhere
measurable ones. Nonsingularity transports their L2 measurability, and the
proved fractional-energy comparison retains the exact canonical Bessel norm.
The finite constant is chosen before the coordinate map and the coefficient. -/
theorem localSobolev_fractional_pullback_ae
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (J L : ℝ≥0) :
    ∃ B : ℝ≥0, ∀ (φ : FourSpace → FourSpace)
      (Dφ : FourSpace → FourSpace →L[ℝ] FourSpace),
      (∀ x, HasFDerivAt φ (Dφ x) x) → Function.Injective φ →
      (∀ x, (1 : ℝ≥0∞) ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(Dφ x).det|) →
      (∀ x y, ‖φ x-φ y‖ ≤ (L : ℝ) * ‖x-y‖) →
      ∀ f : FourSpace → ℝ, LocalSobolevMem α f →
        LocalSobolevMem α (f ∘ φ) ∧
          localSobolevENN α (f ∘ φ) ≤ (B : ℝ≥0∞) * localSobolevENN α f := by
  obtain ⟨A, B, hA, hB, hcompare⟩ :=
    SobolevFractional.localSobolev_fractional_comparison α hα hα1
  let K : ℝ≥0 := ⟨(L : ℝ)^((4:ℝ)+2*α), Real.rpow_nonneg L.coe_nonneg _⟩ * J^2
  let D : ℝ≥0 := A * (J+K) * B
  refine ⟨D+1, ?_⟩
  intro φ Dφ hd hi hJ hL f hmem
  obtain ⟨hf2, hfB⟩ := hmem
  have hg2 : MemLp (complexifyLocal (f ∘ φ)) 2 volume :=
    memLp_comp_of_jacobian_ae φ Dφ hd hi J hJ (complexifyLocal f) hf2
  have hN := eLpNorm_comp_sq_le φ Dφ hd hi J hJ (complexifyLocal f)
  have hE := fractionalDifferenceEnergy_comp_univ_le α hα φ Dφ hd hi J L hJ hL
    (complexifyLocal f)
  have hK : (K : ℝ≥0∞) = ENNReal.ofReal ((L : ℝ)^((4:ℝ)+2*α)) * (J : ℝ≥0∞)^2 := by
    simp only [K, ENNReal.coe_mul, ENNReal.coe_pow]
    rw [ENNReal.ofReal_eq_coe_nnreal (Real.rpow_nonneg L.coe_nonneg _)]
    rfl
  have hsq : localSobolevENN α (f ∘ φ)^2 ≤ (D : ℝ≥0∞) * localSobolevENN α f^2 := by
    calc
      _ ≤ (A : ℝ≥0∞) * ((eLpNorm (complexifyLocal (f ∘ φ)) 2 volume)^2 +
          fractionalDifferenceEnergy α univ (complexifyLocal (f ∘ φ))) :=
        (hcompare (f ∘ φ) hg2).1
      _ ≤ (A : ℝ≥0∞) * ((J : ℝ≥0∞)*(eLpNorm (complexifyLocal f) 2 volume)^2 +
          (K : ℝ≥0∞)*fractionalDifferenceEnergy α univ (complexifyLocal f)) := by
        apply mul_le_mul (le_refl _) _ bot_le bot_le
        apply add_le_add hN
        change fractionalDifferenceEnergy α univ (complexifyLocal f ∘ φ) ≤ _
        rw [hK]
        exact hE
      _ ≤ (A : ℝ≥0∞) * (((J : ℝ≥0∞)+(K : ℝ≥0∞)) *
          ((eLpNorm (complexifyLocal f) 2 volume)^2 +
          fractionalDifferenceEnergy α univ (complexifyLocal f))) := by
        apply mul_le_mul (le_refl _) _ bot_le bot_le
        rw [mul_add]
        apply add_le_add
        · exact mul_le_mul (le_add_right le_rfl) (le_refl _) bot_le bot_le
        · exact mul_le_mul (le_add_left le_rfl) (le_refl _) bot_le bot_le
      _ ≤ (A : ℝ≥0∞) * (((J : ℝ≥0∞)+(K : ℝ≥0∞)) *
          ((B : ℝ≥0∞) * localSobolevENN α f^2)) := by
        apply mul_le_mul (le_refl _) _ bot_le bot_le
        exact mul_le_mul (le_refl _) (hcompare f hf2).2 bot_le bot_le
      _ = _ := by simp only [D, ENNReal.coe_mul, ENNReal.coe_add]; ring
  have hD : (D : ℝ≥0∞) ≤ ((D+1 : ℝ≥0) : ℝ≥0∞)^2 := by
    exact_mod_cast (show D ≤ (D+1)^2 by nlinarith [D.coe_nonneg])
  have hn : localSobolevENN α (f ∘ φ) ≤
      ((D+1 : ℝ≥0) : ℝ≥0∞) * localSobolevENN α f := by
    apply (ENNReal.pow_le_pow_left_iff (by norm_num : (2:ℕ) ≠ 0)).mp
    rw [mul_pow]
    exact hsq.trans (mul_le_mul hD (le_refl _) bot_le bot_le)
  refine ⟨(localSobolevENN_lt_top_iff α (f ∘ φ)).mp ?_, hn⟩
  exact hn.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top
    ((localSobolevENN_lt_top_iff α f).mpr ⟨hf2, hfB⟩))

end K24.Global.SobolevComposition
end K24SOBAECOMP_FractionalPullback_Bundle


/- Inlined source K24SOBAECOMP_Representatives.lean; SHA256 836288bba47a59d945037ac59db1b425f3d162ebc06e1d5a6ea6776471baa147. -/
noncomputable section K24SOBAECOMP_Representatives_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace K24.Global.SobolevComposition

/-- The canonical extended Bessel norm depends only on the almost-everywhere
class of the original real function, including its infinite-value cases. -/
theorem localSobolevENN_congr_ae (s : ℝ) {f g : FourSpace → ℝ}
    (hfg : f =ᵐ[volume] g) : localSobolevENN s f = localSobolevENN s g := by
  have hcomplex : complexifyLocal f =ᵐ[volume] complexifyLocal g := by
    filter_upwards [hfg] with x hx
    simp only [complexifyLocal, hx]
  by_cases hf : MemLp (complexifyLocal f) 2 volume
  · have hg : MemLp (complexifyLocal g) 2 volume := hf.ae_eq hcomplex
    have hdist : localFunctionDistribution f hf = localFunctionDistribution g hg := by
      unfold localFunctionDistribution
      rw [MemLp.toLp_congr hf hg hcomplex]
    simp only [localSobolevENN, dif_pos hf, dif_pos hg, hdist]
  · have hg : ¬ MemLp (complexifyLocal g) 2 volume :=
      fun hg => hf (hg.ae_eq hcomplex.symm)
    simp only [localSobolevENN, dif_neg hf, dif_neg hg]

/-- Original Sobolev membership is likewise a property of the given function's
almost-everywhere class; no continuous realization is used. -/
theorem localSobolevMem_congr_ae (s : ℝ) {f g : FourSpace → ℝ}
    (hfg : f =ᵐ[volume] g) : LocalSobolevMem s f ↔ LocalSobolevMem s g := by
  rw [← localSobolevENN_lt_top_iff, ← localSobolevENN_lt_top_iff,
    localSobolevENN_congr_ae s hfg]

/-- The actual original norm and membership of a pullback are independent
of every null-set change to its coefficient representative, because the
actual Jacobian hypothesis proves nonsingularity of the coordinate map. -/
theorem localSobolev_pullback_congr_ae (s : ℝ)
    (φ : FourSpace → FourSpace) (Dφ : FourSpace → FourSpace →L[ℝ] FourSpace)
    (hd : ∀ x, HasFDerivAt φ (Dφ x) x) (hi : Function.Injective φ)
    (J : ℝ≥0)
    (hJ : ∀ x, (1 : ℝ≥0∞) ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(Dφ x).det|)
    {f g : FourSpace → ℝ} (hfg : f =ᵐ[volume] g) :
    (LocalSobolevMem s (f ∘ φ) ↔ LocalSobolevMem s (g ∘ φ)) ∧
      localSobolevENN s (f ∘ φ) = localSobolevENN s (g ∘ φ) := by
  have hcomp := ae_eq_comp_of_jacobian φ Dφ hd hi J hJ hfg
  exact ⟨localSobolevMem_congr_ae s hcomp, localSobolevENN_congr_ae s hcomp⟩

/-- In particular the standard L2 class representative and the supplied
complex function have equal pullbacks almost everywhere. -/
theorem toLp_comp_ae_of_jacobian
    (φ : FourSpace → FourSpace) (Dφ : FourSpace → FourSpace →L[ℝ] FourSpace)
    (hd : ∀ x, HasFDerivAt φ (Dφ x) x) (hi : Function.Injective φ)
    (J : ℝ≥0)
    (hJ : ∀ x, (1 : ℝ≥0∞) ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(Dφ x).det|)
    (f : FourSpace → ℂ) (hf : MemLp f 2 volume) :
    (hf.toLp f : FourSpace → ℂ) ∘ φ =ᵐ[volume] f ∘ φ :=
  ae_eq_comp_of_jacobian φ Dφ hd hi J hJ hf.coeFn_toLp

end K24.Global.SobolevComposition

end K24SOBAECOMP_Representatives_Bundle


open MeasureTheory
open scoped NNReal ENNReal
open K24.Global in
theorem solution
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (J L : ℝ≥0) :
    ∃ B : ℝ≥0, ∀ (φ : FourSpace → FourSpace)
      (Dφ : FourSpace → FourSpace →L[ℝ] FourSpace),
      (∀ x, HasFDerivAt φ (Dφ x) x) → Function.Injective φ →
      (∀ x, (1 : ℝ≥0∞) ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(Dφ x).det|) →
      (∀ x y, ‖φ x-φ y‖ ≤ (L : ℝ) * ‖x-y‖) →
      ∀ f : FourSpace → ℝ, LocalSobolevMem α f →
        LocalSobolevMem α (f ∘ φ) ∧
          localSobolevENN α (f ∘ φ) ≤ (B : ℝ≥0∞) * localSobolevENN α f := by
  exact K24.Global.SobolevComposition.localSobolev_fractional_pullback_ae α hα hα1 J L

#print axioms solution
#check @solution
