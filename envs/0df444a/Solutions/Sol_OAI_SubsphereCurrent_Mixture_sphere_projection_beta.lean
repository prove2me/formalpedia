-- Prove2me | solution 1 for OAI.SubsphereCurrent.Mixture.sphere_projection_beta
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:40:14.839132+00:00
-- url     : https://prove2.me/submissions/c8bb7928-6955-431b-b778-ddc587d7ab54

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Mixture/BetaTheory.lean:L902-L919
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.Mixture.sphere_projection_beta. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming
import Definitions.Def_OAI_Probability_Subsphere_Kernels_Precision
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Integration
import Definitions.Def_OAI_Probability_Subsphere_Geometry_MassBounds
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Affine
import Definitions.Def_OAI_Probability_Subsphere_Estimates_FixedPrecision
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Haar
import Definitions.Def_OAI_Probability_Subsphere_Mixture_BetaTheory
import Theorems.Thm_OAI_SubsphereCurrent_Mixture_betaSplit_preserving
import Theorems.Thm_OAI_SubsphereCurrent_Mixture_haar_eval_integral

-- ---- from OAI.Probability.Subsphere.Geometry.Integration ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Polar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma introducing_radius :
    MeasurePreserving
      (fun z : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ) => z.2.val • z.1.val)
      ((volume : Measure E).toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E-1)))
      volume := by
  have h₁ := MeasurePreserving.symm (homeomorphUnitSphereProd E).toMeasurableEquiv
    ((volume : Measure E).measurePreserving_homeomorphUnitSphereProd)
  have h₂ := measurePreserving_subtype_coe (μa := (volume : Measure E))
    (measurableSet_singleton (0 : E)).compl
  rw [Measure.restrict_eq_self_of_ae_mem] at h₂
  · exact h₂.comp h₁
  · exact ae_iff.mpr (by simp)

lemma lintegral_polar (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂(volume : Measure E)) =
    ∫⁻ s : Metric.sphere (0 : E) 1, ∫⁻ r : Ioi (0 : ℝ), f (r.val • s.val)
      ∂Measure.volumeIoiPow (Module.finrank ℝ E-1) ∂(volume : Measure E).toSphere := by
  rw [← introducing_radius.lintegral_comp hf]
  exact lintegral_prod _ (hf.comp introducing_radius.measurable).aemeasurable

omit [Nontrivial E] in
lemma orthogonal_sum_volume (H : Submodule ℝ E) :
    MeasurePreserving (fun z : H × Hᗮ => (z.1 : E)+(z.2 : E))
      ((volume : Measure H).prod (volume : Measure Hᗮ)) volume := by
  exact H.orthogonalDecomposition.symm.measurePreserving.comp
    (WithLp.volume_preserving_toLp H Hᗮ)

end SubsphereCurrent.Polar
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Polar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Polar
end
end
section
/-! Isometric naturality of the exact normalized Haar spherical law. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
noncomputable section
namespace SubsphereCurrent.Polar
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

end SubsphereCurrent.Polar
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Slice
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Slice
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Weighted

end SubsphereCurrent.Weighted
end
end
section
open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Polar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Polar
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Slice
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Slice
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Slice
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Slice
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Quarter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end SubsphereCurrent.Quarter
end
end

end OAI

-- ---- from OAI.Probability.Subsphere.Mixture.BetaTheory ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open MeasureTheory Set
open scoped RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory
noncomputable section
namespace SubsphereCurrent.Mixture

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set Module
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

lemma betaJoin_split {z : ℝ × ℝ} (hz : z ∈ betaDomain) : betaJoin (betaSplit z) = z := by
  have hr : z.2 ≠ 0 := ne_of_gt hz.2
  ext <;> simp only [betaSplit,betaJoin]
  · have he : z.1*z.2+(1-z.1)*z.2 = z.2 := by ring
    rw [he,mul_div_cancel_right₀ _ hr]
  · ring

end SubsphereCurrent.Mixture
end
end
section
/-! Exact beta/gamma independence and products, needed to identify the scalar
coordinate laws in the geometric comparison. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

lemma gammaPDF_measurable (a r : ℝ) : Measurable (gammaPDF a r) :=
  (measurable_gammaPDFReal a r).ennreal_ofReal
lemma betaPDF_measurable (a b : ℝ) : Measurable (betaPDF a b) :=
  (measurable_betaPDFReal a b).ennreal_ofReal

lemma lintegral_gamma_eq {f : ℝ → ℝ≥0∞} (hf : Measurable f) (a : ℝ) :
    (∫⁻ x, f x ∂gammaMeasure a 1) = ∫⁻ x in Ioi (0 : ℝ), gammaPDF a 1 x * f x := by
  rw [gammaMeasure,lintegral_withDensity_eq_lintegral_mul volume (gammaPDF_measurable _ _) hf,
    ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr_ae
  have hn : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff]
  filter_upwards [hn] with x hx
  by_cases hp : 0 < x
  · simp [hp]
  · have hneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hx
    simp [hp,gammaPDF_of_neg hneg]

lemma gammaMeasure_restrict_density (a : ℝ) :
    gammaMeasure a 1 = (volume.restrict (Ioi (0 : ℝ))).withDensity (gammaPDF a 1) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_gamma_eq hf,lintegral_withDensity_eq_lintegral_mul _ (gammaPDF_measurable _ _) hf]
  rfl

lemma betaMeasure_restrict_density (a b : ℝ) :
    betaMeasure a b = (volume.restrict (Ioo (0 : ℝ) 1)).withDensity (betaPDF a b) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [betaMeasure,lintegral_withDensity_eq_lintegral_mul _ (betaPDF_measurable _ _) hf,
    lintegral_withDensity_eq_lintegral_mul _ (betaPDF_measurable _ _) hf,
    ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro x
  by_cases h : 0 < x ∧ x < 1
  · simp [h]
  · simp [Set.indicator,betaPDF,betaPDFReal,h]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

lemma square_image_Ioi : (fun r : ℝ => r^2) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
  ext x
  constructor
  · rintro ⟨r,hr,rfl⟩
    exact sq_pos_of_pos (show 0 < r from hr)
  · intro hx
    exact ⟨Real.sqrt x,Real.sqrt_pos.mpr hx,Real.sq_sqrt hx.le⟩

lemma square_inj_Ioi : InjOn (fun r : ℝ => r^2) (Ioi (0 : ℝ)) := by
  intro x hx y hy he
  have hx' : 0 < x := hx
  have hy' : 0 < y := hy
  nlinarith

lemma lintegral_square (f : ℝ → ℝ≥0∞) :
    (∫⁻ x in Ioi (0 : ℝ), f x) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (2*r) * f (r^2) := by
  calc
    _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal |2*r| * f (r^2) := by
      simpa only [square_image_Ioi, Nat.cast_ofNat, show 2-1=1 by decide, pow_one, mul_one, id_eq] using
        (lintegral_image_eq_lintegral_abs_deriv_mul (f := fun r : ℝ => r^2)
          measurableSet_Ioi (fun r _ => ((hasDerivAt_id r).pow 2).hasDerivWithinAt)
          square_inj_Ioi f)
    _ = _ := ?_
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [abs_of_pos (mul_pos (by norm_num) hr)]

lemma gamma_square_density {d : ℕ} (hd : 0 < d) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (2*r) * gammaPDF ((d : ℝ)/2) 1 (r^2) =
      ENNReal.ofReal (2/Real.Gamma ((d : ℝ)/2)) * ENNReal.ofReal (r^(d-1)) *
        ENNReal.ofReal (Real.exp (-(r^2))) := by
  have hd0 : 0 < (d : ℝ)/2 := by positivity
  have hg : 0 < Real.Gamma ((d : ℝ)/2) := Real.Gamma_pos_of_pos hd0
  have hp : r * (r^2)^((d : ℝ)/2-1) = r^(d-1) := by
    rw [← Real.rpow_natCast_mul hr.le]
    calc
      _ = r^(1 : ℝ) * r^((2 : ℝ)*((d : ℝ)/2-1)) := by norm_num only [Real.rpow_one,Nat.cast_ofNat]
      _ = r^((d-1 : ℕ) : ℝ) := by
        rw [← Real.rpow_add hr]
        congr 1
        rw [Nat.cast_sub hd]
        norm_num
        ring
      _ = _ := Real.rpow_natCast r (d-1)
  rw [gammaPDF_of_nonneg (sq_nonneg r)]
  simp only [Real.one_rpow,one_mul]
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  calc
    _ = (2/Real.Gamma ((d : ℝ)/2)) * (r*(r^2)^((d : ℝ)/2-1)) * Real.exp (-(r^2)) := by ring
    _ = _ := by rw [hp]

lemma gamma_sqrt_lintegral (d : ℕ) (hd : 0 < d) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f (Real.sqrt x) ∂gammaMeasure ((d : ℝ)/2) 1) =
      ENNReal.ofReal (2/Real.Gamma ((d : ℝ)/2)) *
        ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(r.val^2))) * f r.val
          ∂Measure.volumeIoiPow (d-1) := by
  rw [lintegral_gamma_eq (f := fun x => f (Real.sqrt x)) (hf.comp (by fun_prop)),lintegral_square]
  have he : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (2*r) *
      (gammaPDF ((d : ℝ)/2) 1 (r^2) * f (Real.sqrt (r^2)))) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (2/Real.Gamma ((d : ℝ)/2)) *
        (ENNReal.ofReal (r^(d-1)) * (ENNReal.ofReal (Real.exp (-(r^2))) * f r)) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [Real.sqrt_sq hr.le,← mul_assoc,gamma_square_density hd hr]
    simp only [mul_assoc]
  rw [he,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  rw [Measure.volumeIoiPow,lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  exact (lintegral_subtype_comap measurableSet_Ioi _).symm

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma gammaSphere_lintegral {f : E → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂gammaSphere (E := E)) = gammaSphereConstant E *
      ∫⁻ x : E, ENNReal.ofReal (Real.exp (-‖x‖^2)) * f x ∂volume := by
  let : IsProbabilityMeasure (gammaMeasure ((Module.finrank ℝ E : ℝ)/2) 1) :=
    isProbabilityMeasure_gammaMeasure (by have := Module.finrank_pos (R := ℝ) (M := E); positivity)
      (by norm_num)
  have hm : Measurable (fun z : Metric.sphere (0 : E) 1 × ℝ => Real.sqrt z.2 • z.1.val) := by fun_prop
  rw [gammaSphere,lintegral_map hf hm]
  rw [lintegral_prod (fun z : Metric.sphere (0 : E) 1 × ℝ => f (Real.sqrt z.2 • z.1.val))
    (hf.comp hm).aemeasurable]
  have hs (s : Metric.sphere (0 : E) 1) :
      (∫⁻ x, f (Real.sqrt x • s.val) ∂gammaMeasure ((Module.finrank ℝ E : ℝ)/2) 1) =
      ENNReal.ofReal (2/Real.Gamma ((Module.finrank ℝ E : ℝ)/2)) *
        ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(r.val^2))) * f (r.val • s.val)
          ∂Measure.volumeIoiPow (Module.finrank ℝ E-1) :=
    gamma_sqrt_lintegral (Module.finrank ℝ E) Module.finrank_pos
      (f := fun r : ℝ => f (r • s.val)) (hf.comp (by fun_prop))
  simp_rw [hs]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,SubsphereRegression.sphereLaw,
    lintegral_smul_measure,Polar.lintegral_polar _ (by fun_prop)]
  simp only [smul_eq_mul,gammaSphereConstant,mul_assoc]
  congr 2
  apply lintegral_congr
  intro s
  apply lintegral_congr
  intro r
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos r.property,
    mem_sphere_zero_iff_norm.mp s.property,mul_one]

lemma gammaSphere_density : gammaSphere (E := E) = gammaSphereConstant E •
    (volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-‖x‖^2))) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [gammaSphere_lintegral hf,lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf]
  rfl

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma invariant_sphere_unique (μ : Measure E) [IsProbabilityMeasure μ]
    (hunit : ∀ᵐ x ∂μ, ‖x‖ = 1)
    (hinv : ∀ u : Orthogonal E, MeasurePreserving (act u) μ μ) :
    μ = SubsphereRegression.ambientSphereLaw := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hm : Measurable (fun z : E × Orthogonal E => f (act z.2 z.1)) :=
    hf.comp (continuous_act.comp continuous_swap).measurable
  calc
    _ = ∫⁻ u : Orthogonal E, ∫⁻ x, f (act u x) ∂μ ∂orthogonalLaw := by
      simp_rw [(hinv _).lintegral_comp hf]
      simp
    _ = ∫⁻ x, ∫⁻ u : Orthogonal E, f (act u x) ∂orthogonalLaw ∂μ :=
      (lintegral_lintegral_swap hm.aemeasurable).symm
    _ = ∫⁻ _x : E, ∫⁻ y, f y ∂SubsphereRegression.ambientSphereLaw ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hunit] with x hx
      exact haar_eval_integral hx hf
    _ = _ := by simp

omit [Nontrivial E] in
lemma measurable_normalize : Measurable (NormedSpace.normalize : E → E) := by
  unfold NormedSpace.normalize
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma normalize_isometry (e : E ≃ₗᵢ[ℝ] E) (x : E) :
    NormedSpace.normalize (e x) = e (NormedSpace.normalize x) := by
  simp [NormedSpace.normalize]

lemma normalized_invariant (μ : Measure E) [IsProbabilityMeasure μ]
    (hnz : ∀ᵐ x ∂μ, x ≠ 0)
    (hinv : ∀ e : E ≃ₗᵢ[ℝ] E, MeasurePreserving e μ μ) :
    μ.map NormedSpace.normalize = SubsphereRegression.ambientSphereLaw := by
  let : IsProbabilityMeasure (μ.map NormedSpace.normalize) :=
    Measure.isProbabilityMeasure_map measurable_normalize.aemeasurable
  apply invariant_sphere_unique
  · rw [ae_map_iff measurable_normalize.aemeasurable (by measurability)]
    exact hnz.mono (fun _ hx => NormedSpace.norm_normalize hx)
  · intro u
    have hm : Measurable (act u : E → E) :=
      (continuous_act.comp (continuous_const.prodMk continuous_id)).measurable
    refine ⟨hm,?_⟩
    rw [Measure.map_map hm measurable_normalize]
    have he : (act u ∘ NormedSpace.normalize : E → E) =
        NormedSpace.normalize ∘ Unitary.linearIsometryEquiv u := by
      funext x
      exact (normalize_isometry (Unitary.linearIsometryEquiv u) x).symm
    rw [he,← Measure.map_map measurable_normalize (Unitary.linearIsometryEquiv u).continuous.measurable,
      (hinv _).map_eq]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [Nontrivial E] in
lemma isotropic_density_preserving (c : ℝ≥0∞) (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving e
      (c • (volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-‖x‖^2))))
      (c • (volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-‖x‖^2)))) := by
  refine ⟨e.continuous.measurable,?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf e.continuous.measurable,lintegral_smul_measure,lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ (f := fun x => ENNReal.ofReal (Real.exp (-‖x‖^2)))
      (g := fun x => f (e x)) (by fun_prop) (hf.comp e.continuous.measurable),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf]
  simp only [smul_eq_mul]
  congr 1
  have hm : Measurable (fun x : E => ENNReal.ofReal (Real.exp (-‖x‖^2)) * f x) := by fun_prop
  simpa only [Pi.mul_apply,e.norm_map] using e.measurePreserving.lintegral_comp hm

lemma normalized_density_uniform (μ : Measure E) [IsProbabilityMeasure μ] {c : ℝ≥0∞}
    (hμ : μ = c • (volume : Measure E).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-‖x‖^2)))) :
    μ.map NormedSpace.normalize = SubsphereRegression.ambientSphereLaw := by
  apply normalized_invariant μ
  · rw [hμ,ae_iff]
    have hz : ((volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-‖x‖^2)))) {0} = 0 :=
      withDensity_absolutelyContinuous _ _ (measure_singleton 0)
    simp only [not_not,Set.ofPred_eq_eq_singleton,Measure.smul_apply,smul_eq_mul,hz,mul_zero]
  · intro e
    rw [hμ]
    exact isotropic_density_preserving c e

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma orthogonal_norm_add (V : Submodule ℝ E) (x : V) (y : Vᗮ) :
    ‖(x : E)+(y : E)‖^2 = ‖x‖^2+‖y‖^2 :=
  by simpa only [pow_two, Submodule.norm_coe] using
    (norm_add_sq_eq_norm_sq_add_norm_sq_real (V.inner_right_of_mem_orthogonal x.prop y.prop))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma orthogonal_exp_mul (V : Submodule ℝ E) (x : V) (y : Vᗮ) :
    ENNReal.ofReal (Real.exp (-‖x‖^2)) * ENNReal.ofReal (Real.exp (-‖y‖^2)) =
      ENNReal.ofReal (Real.exp (-‖(x : E)+(y : E)‖^2)) := by
  rw [← ENNReal.ofReal_mul (by positivity),← Real.exp_add,orthogonal_norm_add]
  congr 2
  ring

omit [Nontrivial E] in
lemma sumGamma_density (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ] :
    sumGamma V = (gammaSphereConstant V * gammaSphereConstant Vᗮ) •
      (volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-‖x‖^2))) := by
  rw [sumGamma,gammaSphere_density,gammaSphere_density,Measure.prod_smul_left,
    Measure.prod_smul_right,smul_smul,Measure.map_smul _ _ _]
  congr 1
  rw [prod_withDensity (by fun_prop) (by fun_prop)]
  apply Measure.ext_of_lintegral
  intro f hf
  have hm : Measurable (fun z : V × Vᗮ => (z.1 : E)+(z.2 : E)) := by fun_prop
  rw [lintegral_map hf hm,
    lintegral_withDensity_eq_lintegral_mul _ (g := fun z : V × Vᗮ => f ((z.1 : E)+(z.2 : E)))
      (by fun_prop) (hf.comp hm),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf]
  simp only [Pi.mul_apply,orthogonal_exp_mul]
  exact (Polar.orthogonal_sum_volume V).lintegral_comp
    (f := fun x : E => ENNReal.ofReal (Real.exp (-‖x‖^2)) * f x) (by fun_prop)

lemma sumGamma_direction (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ] :
    (sumGamma V).map NormedSpace.normalize = SubsphereRegression.ambientSphereLaw :=
  normalized_density_uniform (sumGamma V) (sumGamma_density V)

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

lemma gamma_ae_pos (a : ℝ) : ∀ᵐ x ∂gammaMeasure a 1, 0 < x := by
  rw [gammaMeasure_restrict_density]
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)

lemma beta_ae_mem (a b : ℝ) : ∀ᵐ x ∂betaMeasure a b, x ∈ Ioo (0 : ℝ) 1 := by
  rw [betaMeasure_restrict_density]
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioo)

lemma beta_gamma_ae_domain (a b c : ℝ) (hc : 0 < c) :
    ∀ᵐ z ∂(betaMeasure a b).prod (gammaMeasure c 1), z ∈ betaDomain := by
  let : IsProbabilityMeasure (gammaMeasure c 1) :=
    isProbabilityMeasure_gammaMeasure hc (by norm_num)
  apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioo.prod measurableSet_Ioi)).2
  filter_upwards [beta_ae_mem a b] with x hx
  filter_upwards [gamma_ae_pos c] with y hy
  exact ⟨hx,hy⟩

lemma measurable_betaJoin : Measurable betaJoin := by unfold betaJoin; fun_prop

lemma betaJoin_preserving {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    MeasurePreserving betaJoin ((gammaMeasure a 1).prod (gammaMeasure b 1))
      ((betaMeasure a b).prod (gammaMeasure (a+b) 1)) := by
  refine ⟨measurable_betaJoin,?_⟩
  rw [← (betaSplit_preserving ha hb).map_eq,
    Measure.map_map measurable_betaJoin (by unfold betaSplit; fun_prop)]
  calc
    _ = Measure.map id ((betaMeasure a b).prod (gammaMeasure (a+b) 1)) := by
      apply Measure.map_congr
      filter_upwards [beta_gamma_ae_domain a b (a+b) (add_pos ha hb)] with z hz
      exact betaJoin_split hz
    _ = _ := Measure.map_id

lemma gamma_ratio_preserving {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    MeasurePreserving (fun z : ℝ × ℝ => z.1/(z.1+z.2))
      ((gammaMeasure a 1).prod (gammaMeasure b 1)) (betaMeasure a b) := by
  let : IsProbabilityMeasure (gammaMeasure (a+b) 1) :=
    isProbabilityMeasure_gammaMeasure (add_pos ha hb) (by norm_num)
  exact measurePreserving_fst.comp
    (betaJoin_preserving ha hb)

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma gammaSphere_sqnorm : MeasurePreserving (fun x : E => ‖x‖^2) gammaSphere
    (gammaMeasure ((Module.finrank ℝ E : ℝ)/2) 1) := by
  let : IsProbabilityMeasure (gammaMeasure ((Module.finrank ℝ E : ℝ)/2) 1) :=
    isProbabilityMeasure_gammaMeasure (by have := Module.finrank_pos (R := ℝ) (M := E); positivity)
      (by norm_num)
  have hm : Measurable (fun z : Metric.sphere (0 : E) 1 × ℝ => Real.sqrt z.2 • z.1.val) := by fun_prop
  refine ⟨by fun_prop,?_⟩
  rw [gammaSphere,Measure.map_map (by fun_prop) hm]
  calc
    _ = Measure.map Prod.snd ((SubsphereRegression.sphereLaw (E := E)).prod
      (gammaMeasure ((Module.finrank ℝ E : ℝ)/2) 1)) := by
      apply Measure.map_congr
      have hp : ∀ᵐ z : Metric.sphere (0 : E) 1 × ℝ ∂(SubsphereRegression.sphereLaw (E := E)).prod
          (gammaMeasure ((Module.finrank ℝ E : ℝ)/2) 1), 0 < z.2 :=
        measurePreserving_snd.quasiMeasurePreserving.ae (gamma_ae_pos _)
      filter_upwards [hp] with z hz
      simp only [Function.comp_apply,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _),mem_sphere_zero_iff_norm.mp z.1.property,mul_one]
      exact Real.sq_sqrt hz.le
    _ = _ := measurePreserving_snd.map_eq

end SubsphereCurrent.Mixture
end
end
section
/-! Actual squared-projection beta law of the normalized Haar sphere. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma normalize_sum_sqproj (V : Submodule ℝ E) (x : V) (y : Vᗮ) :
    ‖V.orthogonalProjectionOnto (NormedSpace.normalize ((x : E)+(y : E)))‖^2 =
      ‖x‖^2/(‖x‖^2+‖y‖^2) := by
  rw [NormedSpace.normalize,map_smul,map_add,
    V.orthogonalProjectionOnto_apply_of_mem_orthogonal y.property]
  simp only [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,add_zero,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),mul_pow,inv_pow,
    orthogonal_norm_add,div_eq_mul_inv,mul_comm]

lemma sphere_projection_beta (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ] :
    MeasurePreserving (fun x : E => ‖V.orthogonalProjectionOnto x‖^2)
      SubsphereRegression.ambientSphereLaw
      (betaMeasure ((Module.finrank ℝ V : ℝ)/2) ((Module.finrank ℝ Vᗮ : ℝ)/2)) := by
  have ha : 0 < (Module.finrank ℝ V : ℝ)/2 := by have := Module.finrank_pos (R := ℝ) (M := V); positivity
  have hb : 0 < (Module.finrank ℝ Vᗮ : ℝ)/2 := by have := Module.finrank_pos (R := ℝ) (M := Vᗮ); positivity
  have h : MeasurePreserving (fun z : V × Vᗮ => ‖z.1‖^2/(‖z.1‖^2+‖z.2‖^2))
      ((gammaSphere (E := V)).prod (gammaSphere (E := Vᗮ)))
      (betaMeasure ((Module.finrank ℝ V : ℝ)/2) ((Module.finrank ℝ Vᗮ : ℝ)/2)) :=
    (gamma_ratio_preserving ha hb).comp (gammaSphere_sqnorm.prod gammaSphere_sqnorm)
  refine ⟨by fun_prop,?_⟩
  have hp : Measurable (fun x : E => ‖V.orthogonalProjectionOnto x‖^2) := by fun_prop
  rw [← sumGamma_direction V,Measure.map_map hp measurable_normalize,
    sumGamma,Measure.map_map (hp.comp measurable_normalize) (by fun_prop)]
  convert h.map_eq using 1
  congr 1
  funext z
  exact normalize_sum_sqproj V z.1 z.2

end SubsphereCurrent.Mixture
end
end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Mixture
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.Mixture.sphere_projection_beta := @_root_.OAI.SubsphereCurrent.Mixture.sphere_projection_beta
