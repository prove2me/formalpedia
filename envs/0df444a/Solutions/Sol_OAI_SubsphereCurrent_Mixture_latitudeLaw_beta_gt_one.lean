-- Prove2me | solution 1 for OAI.SubsphereCurrent.Mixture.latitudeLaw_beta_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:50:48.577707+00:00
-- url     : https://prove2.me/submissions/4422e5c3-6750-4cef-844b-0ecdb99e814f

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Mixture/Latitude.lean:L268-L313
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.Mixture.latitudeLaw_beta_gt_one. The node keeps its source
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
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Latitude
import Theorems.Thm_OAI_SubsphereCurrent_Mixture_betaSplit_preserving
import Theorems.Thm_OAI_SubsphereCurrent_Mixture_sphere_projection_beta

-- ---- from OAI.Probability.Subsphere.Mixture.Haar ----
namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma act_norm (u : Orthogonal E) (x : E) : ‖act u x‖ = ‖x‖ := Unitary.norm_map u x

variable [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
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
noncomputable section
universe u v w
namespace SubsphereCurrent

end SubsphereCurrent
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

lemma nested_starProjection (U N : Submodule ℝ E) (h : U ≤ N) (x : N) :
    (((U.comap N.subtype).starProjection x : N) : E) = U.starProjection (x : E) := by
  have he : (U.comap N.subtype).starProjection x =
      (⟨U.starProjection (x : E), h (U.orthogonalProjectionOnto (x : E)).prop⟩ : N) := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact (U.orthogonalProjectionOnto (x : E)).prop
    · intro w hw
      exact U.starProjection_inner_eq_zero (x : E) (w : E) hw
  exact congrArg Subtype.val he

lemma nested_projection_norm (U N : Submodule ℝ E) (h : U ≤ N) (x : N) :
    ‖(U.comap N.subtype).orthogonalProjectionOnto x‖ = ‖U.orthogonalProjectionOnto (x : E)‖ := by
  exact congrArg norm (nested_starProjection U N h x)

omit [FiniteDimensional ℝ E] in
lemma nested_rank (U N : Submodule ℝ E) (h : U ≤ N) :
    Module.finrank ℝ (U.comap N.subtype) = Module.finrank ℝ U :=
  (Submodule.comapSubtypeEquivOfLe h).finrank_eq

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

lemma measurable_perpCoordinate (V : Submodule ℝ E) : Measurable (perpCoordinate V) := by
  unfold perpCoordinate
  fun_prop

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

omit [MeasurableSpace E] [BorelSpace E] in
lemma perpCoordinate_blockIso (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) (x : E) :
    perpCoordinate V (blockIso V u w x) = perpCoordinate V x := by
  rw [perpCoordinate,blockIso_apply,map_add,
    Vᗮ.orthogonalProjectionOnto_apply_of_mem_orthogonal (by simp)]
  simp [perpCoordinate,act_norm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma latitude_perp_le (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1) :
    Vᗮ ≤ latitudeSpace V e := by
  apply Submodule.orthogonal_le
  exact Submodule.span_le.mpr (by simp)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma latitude_e_norm (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1) : ‖(e.val : E)‖ = 1 :=
  mem_sphere_zero_iff_norm.mp e.prop

omit [MeasurableSpace E] [BorelSpace E] in
lemma latitude_rank (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1) :
    Module.finrank ℝ (latitudeSpace V e)+1 = Module.finrank ℝ E := by
  have he : (e.val : E) ≠ 0 := by intro h; have := latitude_e_norm V e; simp [h] at this
  have h := (ℝ ∙ (e.val : E)).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton he] at h
  change Module.finrank ℝ (ℝ ∙ (e.val : E))ᗮ + 1 = Module.finrank ℝ E
  exact (Nat.add_comm _ _).trans h

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

lemma gamma_prod_ae_domain (a b : ℝ) (hb : 0 < b) :
    ∀ᵐ z ∂(gammaMeasure a 1).prod (gammaMeasure b 1), z ∈ gammaDomain := by
  let : IsProbabilityMeasure (gammaMeasure b 1) :=
    isProbabilityMeasure_gammaMeasure hb (by norm_num)
  apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioi.prod measurableSet_Ioi)).2
  filter_upwards [gamma_ae_pos a] with x hx
  filter_upwards [gamma_ae_pos b] with y hy
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

lemma gamma_sum_preserving {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    MeasurePreserving (fun z : ℝ × ℝ => z.1+z.2)
      ((gammaMeasure a 1).prod (gammaMeasure b 1)) (gammaMeasure (a+b) 1) := by
  let : IsProbabilityMeasure (gammaMeasure (a+b) 1) :=
    isProbabilityMeasure_gammaMeasure (add_pos ha hb) (by norm_num)
  let : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasureBeta ha hb
  exact measurePreserving_snd.comp
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

end SubsphereCurrent.Mixture
end
end

end OAI

-- ---- from OAI.Probability.Subsphere.Mixture.Latitude ----
namespace OAI

noncomputable section

namespace SubsphereCurrent.Mixture
section
open MeasureTheory ProbabilityTheory Set

section
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma nested_projection_beta (U N : Submodule ℝ E) (hUN : U ≤ N)
    (hU : 0 < Module.finrank ℝ U) (hN : Module.finrank ℝ U < Module.finrank ℝ N) :
    MeasurePreserving (fun x : N => ‖U.orthogonalProjectionOnto (x : E)‖^2)
      SubsphereRegression.ambientSphereLaw
      (betaMeasure ((Module.finrank ℝ U : ℝ)/2)
        (((Module.finrank ℝ N : ℝ)-(Module.finrank ℝ U : ℝ))/2)) := by
  let H := U.comap N.subtype
  have hH : Module.finrank ℝ H = Module.finrank ℝ U := nested_rank U N hUN
  have hdim := H.finrank_add_finrank_orthogonal
  have hHc : 0 < Module.finrank ℝ Hᗮ := by omega
  let : Nontrivial N := Module.nontrivial_of_finrank_pos (R := ℝ) (M := N) (by omega)
  let : Nontrivial H := Module.nontrivial_of_finrank_pos (hH ▸ hU)
  let : Nontrivial Hᗮ := Module.nontrivial_of_finrank_pos hHc
  have hc : (Module.finrank ℝ Hᗮ : ℝ) =
      (Module.finrank ℝ N : ℝ)-(Module.finrank ℝ U : ℝ) := by
    have hd : (Module.finrank ℝ H : ℝ)+(Module.finrank ℝ Hᗮ : ℝ) = Module.finrank ℝ N := by
      exact_mod_cast hdim
    rw [hH] at hd
    linarith
  have he : (fun x : N => ‖H.orthogonalProjectionOnto x‖^2) =
      (fun x : N => ‖U.orthogonalProjectionOnto (x : E)‖^2) := by
    funext x
    rw [nested_projection_norm U N hUN]
  simpa only [he,hH,hc] using sphere_projection_beta H

omit [MeasurableSpace E] [BorelSpace E] in
lemma latitude_coordinate (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    (u : Orthogonal V) (x : latitudeSpace V e) {q : ℝ} (hq : 0 ≤ q) :
    perpCoordinate V (blockIso V u 1
      (Real.sqrt (1-q) • (e.val : E)+Real.sqrt q • (x : E))) =
      q * perpCoordinate V (x : E) := by
  rw [perpCoordinate_blockIso,perpCoordinate,map_add,map_smul,map_smul,
    Vᗮ.orthogonalProjectionOnto_apply_of_mem_orthogonal (by simp)]
  simp only [smul_zero,zero_add,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt hq,perpCoordinate]

lemma measurable_latitudeSampler (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1) :
    Measurable (fun z : ℝ × (Orthogonal V × latitudeSpace V e) => blockIso V z.2.1 1
      (Real.sqrt (1-z.1) • (e.val : E)+Real.sqrt z.1 • (z.2.2 : E))) :=
  ((continuous_blockIso V).comp
    (((continuous_fst.comp continuous_snd).prodMk continuous_const).prodMk
      (((continuous_const.sub continuous_fst).sqrt.smul continuous_const).add
        (continuous_fst.sqrt.smul (continuous_subtype_val.comp
          (continuous_snd.comp continuous_snd)))))).measurable

end
open scoped ENNReal NNReal

lemma beta_product_preserving {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    MeasurePreserving (fun z : ℝ × ℝ => z.1*z.2)
      ((betaMeasure a b).prod (betaMeasure (a+b) c)) (betaMeasure a (b+c)) := by
  let : IsProbabilityMeasure (gammaMeasure a 1) := isProbabilityMeasure_gammaMeasure ha (by norm_num)
  let : IsProbabilityMeasure (gammaMeasure b 1) := isProbabilityMeasure_gammaMeasure hb (by norm_num)
  let : IsProbabilityMeasure (gammaMeasure c 1) := isProbabilityMeasure_gammaMeasure hc (by norm_num)
  let : IsProbabilityMeasure (gammaMeasure (a+b) 1) :=
    isProbabilityMeasure_gammaMeasure (add_pos ha hb) (by norm_num)
  let : IsProbabilityMeasure (gammaMeasure (b+c) 1) :=
    isProbabilityMeasure_gammaMeasure (add_pos hb hc) (by norm_num)
  let : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasureBeta ha hb
  let μ := ((gammaMeasure a 1).prod (gammaMeasure b 1)).prod (gammaMeasure c 1)
  have hF : MeasurePreserving
      (fun z : (ℝ × ℝ) × ℝ => (z.1.1/(z.1.1+z.1.2),(z.1.1+z.1.2)/(z.1.1+z.1.2+z.2)))
      μ ((betaMeasure a b).prod (betaMeasure (a+b) c)) := by
    exact ((MeasurePreserving.id (betaMeasure a b)).prod (gamma_ratio_preserving (add_pos ha hb) hc)).comp
      ((measurePreserving_prodAssoc (betaMeasure a b) (gammaMeasure (a+b) 1) (gammaMeasure c 1)).comp
        ((betaJoin_preserving ha hb).prod (MeasurePreserving.id (gammaMeasure c 1))))
  have hG : MeasurePreserving (fun z : (ℝ × ℝ) × ℝ => z.1.1/(z.1.1+(z.1.2+z.2)))
      μ (betaMeasure a (b+c)) := by
    exact (gamma_ratio_preserving ha (add_pos hb hc)).comp
      (((MeasurePreserving.id (gammaMeasure a 1)).prod (gamma_sum_preserving hb hc)).comp
        (measurePreserving_prodAssoc (gammaMeasure a 1) (gammaMeasure b 1) (gammaMeasure c 1)))
  refine ⟨by fun_prop,?_⟩
  rw [← hF.map_eq,Measure.map_map (by fun_prop) hF.measurable]
  calc
    _ = Measure.map (fun z : (ℝ × ℝ) × ℝ => z.1.1/(z.1.1+(z.1.2+z.2))) μ := by
      apply Measure.map_congr
      have hpos : ∀ᵐ z : (ℝ × ℝ) × ℝ ∂μ, 0 < z.1.1 ∧ 0 < z.1.2 :=
        (measurePreserving_fst.quasiMeasurePreserving.ae (gamma_prod_ae_domain a b hb))
      filter_upwards [hpos] with z hz
      dsimp only [Function.comp_apply]
      rw [← mul_div_assoc,div_mul_cancel₀ _ (add_pos hz.1 hz.2).ne',add_assoc]
    _ = _ := hG.map_eq

end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma latitudeLaw_beta_gt_one (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    (hV : 1 < Module.finrank ℝ V) (hD : Module.finrank ℝ V < Module.finrank ℝ E)
    {a delta : ℝ} (ha : 0 < a) (hd : 0 < delta)
    (hshape : a+delta = ((Module.finrank ℝ E : ℝ)-(Module.finrank ℝ V : ℝ))/2) :
    MeasurePreserving (perpCoordinate V) (latitudeLaw V e a delta)
      (betaMeasure a (delta+((Module.finrank ℝ V : ℝ)-1)/2)) := by
  have hr := latitude_rank V e
  have hk := V.finrank_add_finrank_orthogonal
  have hK : 0 < Module.finrank ℝ Vᗮ := by omega
  have hKL : Module.finrank ℝ Vᗮ < Module.finrank ℝ (latitudeSpace V e) := by omega
  let : Nontrivial (latitudeSpace V e) := Module.nontrivial_of_finrank_pos
    (R := ℝ) (M := latitudeSpace V e) (by omega)
  let : IsProbabilityMeasure (betaMeasure a delta) := isProbabilityMeasureBeta ha hd
  have hA : (Module.finrank ℝ Vᗮ : ℝ)/2 = a+delta := by
    have hk' : (Module.finrank ℝ V : ℝ)+(Module.finrank ℝ Vᗮ : ℝ) = Module.finrank ℝ E := by exact_mod_cast hk
    linarith
  have hC : ((Module.finrank ℝ (latitudeSpace V e) : ℝ)-(Module.finrank ℝ Vᗮ : ℝ))/2 =
      ((Module.finrank ℝ V : ℝ)-1)/2 := by
    have hk' : (Module.finrank ℝ V : ℝ)+(Module.finrank ℝ Vᗮ : ℝ) = Module.finrank ℝ E := by exact_mod_cast hk
    have hr' : (Module.finrank ℝ (latitudeSpace V e) : ℝ)+1 = Module.finrank ℝ E := by exact_mod_cast hr
    linarith
  have hcoord : MeasurePreserving (fun x : latitudeSpace V e => perpCoordinate V (x : E))
      SubsphereRegression.ambientSphereLaw (betaMeasure (a+delta) (((Module.finrank ℝ V : ℝ)-1)/2)) := by
    simpa only [hA,hC,perpCoordinate] using
      nested_projection_beta Vᗮ (latitudeSpace V e) (latitude_perp_le V e) hK hKL
  have hc : 0 < ((Module.finrank ℝ V : ℝ)-1)/2 := by
    have hvr : (1 : ℝ) < Module.finrank ℝ V := by exact_mod_cast hV
    linarith
  have hpair := (MeasurePreserving.id (betaMeasure a delta)).prod
    (hcoord.comp (measurePreserving_snd (μ := orthogonalLaw (E := V))))
  have hprod := (beta_product_preserving ha hd hc).comp hpair
  refine ⟨measurable_perpCoordinate V,?_⟩
  rw [latitudeLaw,Measure.map_map (measurable_perpCoordinate V) (measurable_latitudeSampler V e)]
  calc
    _ = Measure.map (fun z : ℝ × (Orthogonal V × latitudeSpace V e) =>
        z.1 * perpCoordinate V (z.2.2 : E))
        ((betaMeasure a delta).prod ((orthogonalLaw (E := V)).prod
          SubsphereRegression.ambientSphereLaw)) := by
      apply Measure.map_congr
      have hq : ∀ᵐ z : ℝ × (Orthogonal V × latitudeSpace V e)
          ∂(betaMeasure a delta).prod ((orthogonalLaw (E := V)).prod SubsphereRegression.ambientSphereLaw),
          z.1 ∈ Ioo (0 : ℝ) 1 :=
        measurePreserving_fst.quasiMeasurePreserving.ae (beta_ae_mem a delta)
      filter_upwards [hq] with z hz
      exact latitude_coordinate V e z.2.1 z.2.2 hz.1.le
    _ = _ := hprod.map_eq

end SubsphereCurrent.Mixture

end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Mixture
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.Mixture.latitudeLaw_beta_gt_one := @_root_.OAI.SubsphereCurrent.Mixture.latitudeLaw_beta_gt_one
