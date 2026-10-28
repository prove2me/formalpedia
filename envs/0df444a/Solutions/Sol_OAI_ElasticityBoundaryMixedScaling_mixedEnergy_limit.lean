-- Prove2me | solution 1 for OAI.ElasticityBoundaryMixedScaling.mixedEnergy_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:50:04.831681+00:00
-- url     : https://prove2.me/submissions/0efc33f1-50d4-4e23-bb2a-954e2af016f5

import Mathlib
import Definitions.Def_OAIQ6El001
import Theorems.Thm_OAI_ElasticityBoundaryCutoffParametrix_first_scaled_identity
import Theorems.Thm_OAI_ElasticityBoundaryEnergyLimit_mixed_scaled_limit

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Exact anisotropic boundary scaling, retaining the physical dimension-three
Jacobian δ⁴. No asymptotic change-of-variable formula is postulated. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryScaling

lemma scale_comp (δ ε : ℝ) (y : Y) : scale δ (scale ε y) = scale (δ*ε) y := by
  ext i
  simp only [scale_apply, scaleFactor]
  split_ifs <;> ring

lemma scale_inv (δ : ℝ) (hδ : δ≠0) (y : Y) : scale δ (scale δ⁻¹ y) = y := by
  rw [scale_comp, mul_inv_cancel₀ hδ, scale_one]

lemma scale_injective (δ : ℝ) (hδ : δ≠0) : Function.Injective (scale δ) := by
  intro y z h
  have := congrArg (scale δ⁻¹) h
  simpa only [scale_comp, inv_mul_cancel₀ hδ, scale_one] using this

lemma scale_surjective (δ : ℝ) (hδ : δ≠0) : Function.Surjective (scale δ) :=
  fun y => ⟨scale δ⁻¹ y, scale_inv δ hδ y⟩

lemma scale_det (δ : ℝ) : (scale δ).det = δ^4 := by
  change LinearMap.det (LinearMap.pi (fun i : Fin 3 =>
    (scaleFactor δ i • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).comp (LinearMap.proj i))) = _
  rw [LinearMap.det_pi]
  simp [scaleFactor, Fin.prod_univ_three]
  ring

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Exact full-space change of variables; valid even when the integral is the
Bochner fallback zero, and for vector-valued functions. -/
theorem integral_scale {δ : ℝ} (hδ : δ≠0) (f : Y → F) :
    (∫ y, f y) = δ^4 • ∫ y, f (scale δ y) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure Y)
    (f := scale δ) (f' := fun _ => scale δ) MeasurableSet.univ
    (fun y _ => (scale δ).hasFDerivAt.hasFDerivWithinAt)
    (scale_injective δ hδ).injOn f
  simpa only [image_univ, (scale_surjective δ hδ).range_eq, Measure.restrict_univ,
    scale_det, abs_of_nonneg (show 0 ≤ δ^4 by positivity), integral_smul] using h

end ElasticityBoundaryScaling

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundarySymbols
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Literal anisotropic oscillatory Gaussian boundary profiles, with actual
Frechet derivatives.  The small parameter is never assigned a symbolic DN map. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryProfile
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryScaling ElasticityBoundaryWeights

lemma phase_real (δ : ℝ) (y : Y) : (value (phase δ) y).re = -y 2-(y 0)^2-(y 1)^2 := by
  simp [phase, value, Complex.div_re, ← Complex.ofReal_pow]
  ring

lemma envelope_norm (δ : ℝ) (y : Y) :
    ‖envelope δ y‖=Real.exp (-y 2-(y 0)^2-(y 1)^2) := by
  rw [envelope, Complex.norm_exp, phase_real]

/-- Modulus squared is the proved integrable Gaussian/normal weight; the fast
oscillation does not alter it at any nonzero scale. -/
theorem profile_square_weight (δ : ℝ) (p : MP) (y : Y) :
    ({y : Y | 0<y 2} : Set Y).indicator (fun y => ‖profile δ p y‖^2) y =
      ‖value p y‖^2 * weight 2 y := by
  by_cases hy : 0<y 2
  · simp [Set.indicator, hy, profile, mul_pow, envelope_norm,
      weight, Fin.prod_univ_three, factor]
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    rw [mul_comm (Real.exp _)]
    congr 2
    ring
  · simp [Set.indicator, hy, weight, Fin.prod_univ_three, factor]

end ElasticityBoundaryProfile

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryLayers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Honest L2 bounds and exact change of variables for physical boundary layers. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryProfileBounds
open ElasticityBoundaryMVCalculus ElasticityBoundaryScaling ElasticityBoundaryWeights
  ElasticityBoundaryProfile
lemma measurable_halfspace : MeasurableSet halfspace :=
  (isOpen_lt continuous_const (continuous_apply 2)).measurableSet

lemma scale_mem_halfspace {δ : ℝ} (hδ : δ≠0) (y : Y) : scale δ y ∈ halfspace ↔ y∈halfspace := by
  change 0 < scale δ y 2 ↔ 0<y 2
  simp only [scale_apply, scaleFactor]
  exact mul_pos_iff_of_pos_left (sq_pos_of_ne_zero hδ)

lemma scale_indicator {F : Type*} [Zero F] {δ : ℝ} (hδ : δ≠0) (f : Y → F) (y : Y) :
    halfspace.indicator f (scale δ y)=halfspace.indicator (fun y => f (scale δ y)) y := by
  classical
  change (if scale δ y ∈ halfspace then _ else 0) = (if y∈halfspace then _ else 0)
  rw [scale_mem_halfspace hδ]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem integralOn_scale {δ : ℝ} (hδ : δ≠0) (f : Y → F) :
    (∫ y in halfspace, f y) = δ^4 • ∫ y in halfspace, f (scale δ y) := by
  rw [← integral_indicator measurable_halfspace, integral_scale hδ]
  simp_rw [scale_indicator hδ]
  rw [integral_indicator measurable_halfspace]

end ElasticityBoundaryProfileBounds

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityBoundaryLimit
/-! Genuine Gaussian boundary scaling limits for the finite corrected
amplitudes. Dominated convergence is proved from the uniform polynomial
majorants and the actual half-space weight. -/
open Set Filter MeasureTheory
open scoped Topology BigOperators
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryScaling ElasticityBoundaryWeights ElasticityBoundaryOrderBound
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundaryCutoffParametrix
  ElasticityBoundaryProfileBounds ElasticityBoundaryCutoffLayer

lemma eventually_small_positive : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0<δ ∧ δ≤1 := by
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with δ hδ h1
  exact ⟨hδ,h1.le⟩

end ElasticityBoundaryLimit
namespace ElasticityBoundaryMixedScaling
/-! Exact physical mixed-energy Jacobian cancellation, followed by the actual
boundary limit. These integrals contain literal Frechet derivatives of the
cut-off corrected fields. -/
open Set Filter MeasureTheory
open scoped Topology BigOperators
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryScaling ElasticityBoundaryWeights ElasticityBoundaryOrderBound
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundaryCutoffParametrix ElasticityBoundaryLimit
  ElasticityBoundaryProfileBounds ElasticityBoundaryCutoffLayer ElasticityBoundaryProfile
  ElasticityBoundaryCutoffBound ElasticityBoundaryEnergyLimit ElasticityBoundaryStrongLayer

lemma envelope_product_weight (δ : ℝ) (g : Y → ℂ) (y : Y) :
    halfspace.indicator (fun z => envelope δ z*star (envelope δ z)*g z) y=
      weight 2 y • g y := by
  have h := profile_square_weight δ (C 1) y
  simp only [profile,value_C,mul_one,norm_one,one_pow,one_mul] at h
  change halfspace.indicator (fun z => ‖envelope δ z‖^2) y=weight 2 y at h
  by_cases hy : y∈halfspace
  · rw [indicator_of_mem hy] at h ⊢
    rw [show envelope δ y*star (envelope δ y)=(‖envelope δ y‖:ℂ)^2 from Complex.mul_conj' _]
    rw [← Complex.ofReal_pow,h,Complex.real_smul]
  · rw [indicator_of_notMem hy] at h ⊢
    rw [← h,zero_smul]

lemma integral_envelope_mixed (δ : ℝ) (g : Y → ℂ) :
    (∫ y in halfspace, envelope δ y*star (envelope δ y)*g y)=
      ∫ y, weight 2 y • g y := by
  rw [← integral_indicator measurable_halfspace]
  exact integral_congr_ae (Eventually.of_forall (envelope_product_weight δ g))

/-- The factor delta^(2n) comes from the true normal coordinate, while the
volume delta^4 cancels the two true first derivatives delta^-2. -/
theorem mixedEnergy_scaled (n : ℕ) (H : Y → ℂ) {χ : Y → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (p q : Polynomial W) (i α j β : Fin 3)
    {δ : ℝ} (hδ : δ≠0) :
    ((δ^(2*n))⁻¹:ℝ) • mixedEnergy n H χ p q i α j β δ=
      ∫ y, weight 2 y • mixedScaled n H χ p q i α j β δ y := by
  unfold mixedEnergy
  rw [integralOn_scale hδ]
  have he (y : Y) :
      ((scale δ y 2:ℝ):ℂ)^n*H (scale δ y)*dpart (cutoffLayer χ p δ i) α (scale δ y)*
        star (dpart (cutoffLayer χ q δ j) β (scale δ y))=
      (δ^(2*n)*(δ^4)⁻¹:ℝ) • (envelope δ y*star (envelope δ y)*
        mixedScaled n H χ p q i α j β δ y) := by
    rw [first_scaled_identity hχ hδ,first_scaled_identity hχ hδ]
    simp only [scale_apply,scaleFactor,ite_true,Complex.real_smul,star_mul,Complex.star_def,
      Complex.conj_ofReal,mixedScaled]
    push_cast
    rw [mul_pow,← pow_mul]
    have hd : (δ:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hδ
    field_simp
  simp_rw [he]
  rw [integral_smul,integral_envelope_mixed,smul_smul,smul_smul]
  have hs : ((δ^(2*n))⁻¹*δ^4)*(δ^(2*n)*(δ^4)⁻¹)=1 := by field_simp
  rw [hs,one_smul]

theorem mixedEnergy_limit_oai (n : ℕ) {H χ : Y → ℂ} (hH : Continuous H) (hcH : HasCompactSupport H)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcχ : HasCompactSupport χ) (h0 : χ 0=1)
    (p q : Polynomial W) (i α j β : Fin 3) :
    Tendsto (fun δ => ((δ^(2*n))⁻¹:ℝ) • mixedEnergy n H χ p q i α j β δ) (𝓝[>] 0)
      (𝓝 (∫ y : Y, weight 2 y • ((y 2:ℂ)^n*H 0*
        value (E₀ α (p.coeff 0 i)) y*star (value (E₀ β (q.coeff 0 j)) y)))) := by
  apply (mixed_scaled_limit n hH hcH hχ hcχ h0 p q i α j β).congr'
  filter_upwards [eventually_small_positive] with δ hδ
  exact (mixedEnergy_scaled n H hχ p q i α j β hδ.1.ne').symm

end ElasticityBoundaryMixedScaling

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityBoundaryMixedScaling.mixedEnergy_limit_oai := @OAI.ElasticityBoundaryMixedScaling.mixedEnergy_limit_oai
