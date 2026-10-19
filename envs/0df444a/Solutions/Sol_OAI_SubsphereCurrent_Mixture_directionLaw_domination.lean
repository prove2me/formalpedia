-- Prove2me | solution 1 for OAI.SubsphereCurrent.Mixture.directionLaw_domination
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:57:16.492996+00:00
-- url     : https://prove2.me/submissions/a5a03972-1ccd-431e-9c87-3f24614088e2

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Mixture/Domination.lean:L219-L294
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.Mixture.directionLaw_domination. The node keeps its source
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
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Domination
import Theorems.Thm_OAI_SubsphereCurrent_Mixture_block_average_unit
import Theorems.Thm_OAI_SubsphereCurrent_Mixture_directionLaw_beta
import Theorems.Thm_OAI_SubsphereCurrent_Mixture_directionLaw_invariant
import Theorems.Thm_OAI_SubsphereCurrent_Mixture_latitudeLaw_beta_gt_one
import Theorems.Thm_OAI_SubsphereCurrent_Mixture_latitudeLaw_beta_one
import Theorems.Thm_OAI_SubsphereCurrent_Mixture_latitudeLaw_invariant
import Theorems.Thm_OAI_SubsphereCurrent_Mixture_latitudeLaw_unit
import Theorems.Thm_OAI_SubsphereCurrent_Mixture_sphere_projection_beta
import Theorems.Thm_OAI_SubsphereCurrent_rpow_decrease_shift
import Theorems.Thm_OAI_SubsphereRegression_ambientSphereLaw_isometry

-- ---- from OAI.Probability.Subsphere.Regression.Spheres ----
namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
section SphereBounds
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SphereBounds

open scoped Pointwise
section MoreSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma ambientSphereLaw_support : (ambientSphereLaw (E := E)).support ⊆ Metric.sphere 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_sphere
  rw [mem_ae_iff, ambientSphereLaw, Measure.map_apply (by fun_prop)
    Metric.isClosed_sphere.measurableSet.compl]
  have h : (Subtype.val : Metric.sphere (0 : E) 1 → E) ⁻¹' (Metric.sphere 0 1)ᶜ = ∅ := by
    ext x
    simp
  rw [h, measure_empty]

lemma ambientSphereLaw_ae_norm [Nontrivial E] :
    ∀ᵐ x : E ∂ambientSphereLaw, ‖x‖ = 1 := by
  filter_upwards [Measure.support_mem_ae (μ := ambientSphereLaw (E := E))] with x hx
  exact mem_sphere_zero_iff_norm.mp (ambientSphereLaw_support hx)

end MoreSphere

section FubiniAux
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
end FubiniAux

end SubsphereRegression
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

lemma measurable_perpCoordinate (V : Submodule ℝ E) : Measurable (perpCoordinate V) := by
  unfold perpCoordinate
  fun_prop

lemma measurable_mixtureSampler (V : Submodule ℝ E) : Measurable (mixtureSampler V) := by
  unfold mixtureSampler
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

lemma directionLaw_unit (V N : Submodule ℝ E) [Nontrivial N] :
    ∀ᵐ x ∂directionLaw V N, ‖x‖ = 1 := by
  rw [directionLaw,ae_map_iff (measurable_directionSampler V N).aemeasurable (by measurability)]
  have h : ∀ᵐ z : Orthogonal Vᗮ × N ∂(orthogonalLaw (E := Vᗮ)).prod
      SubsphereRegression.ambientSphereLaw, ‖z.2‖ = 1 :=
    measurePreserving_snd.quasiMeasurePreserving.ae SubsphereRegression.ambientSphereLaw_ae_norm
  filter_upwards [h] with z hz
  simpa using hz

lemma measurable_latitudeSampler (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1) :
    Measurable (fun z : ℝ × (Orthogonal V × latitudeSpace V e) => blockIso V z.2.1 1
      (Real.sqrt (1-z.1) • (e.val : E)+Real.sqrt z.1 • (z.2.2 : E))) :=
  ((continuous_blockIso V).comp
    (((continuous_fst.comp continuous_snd).prodMk continuous_const).prodMk
      (((continuous_const.sub continuous_fst).sqrt.smul continuous_const).add
        (continuous_fst.sqrt.smul (continuous_subtype_val.comp
          (continuous_snd.comp continuous_snd)))))).measurable

lemma latitudeLaw_probability (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1)
    [Nontrivial (latitudeSpace V e)] {a delta : ℝ} (ha : 0 < a) (hd : 0 < delta) :
    IsProbabilityMeasure (latitudeLaw V e a delta) := by
  let : IsProbabilityMeasure (betaMeasure a delta) := isProbabilityMeasureBeta ha hd
  unfold latitudeLaw
  exact Measure.isProbabilityMeasure_map (measurable_latitudeSampler V e).aemeasurable

end
open scoped ENNReal NNReal

end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture

end

end OAI

-- ---- from OAI.Probability.Subsphere.Mixture.Domination ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma block_classification (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ]
    (μ : Measure E) [SFinite μ] (hunit : ∀ᵐ x ∂μ, ‖x‖ = 1)
    (hinv : ∀ (u : Orthogonal V) (w : Orthogonal Vᗮ), MeasurePreserving (blockIso V u w) μ μ) :
    μ = mixtureLaw V (μ.map (perpCoordinate V)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  let η := (SubsphereRegression.ambientSphereLaw (E := V)).prod
    (SubsphereRegression.ambientSphereLaw (E := Vᗮ))
  have hPhi : Measurable (fun q : ℝ => ∫⁻ z : V × Vᗮ, f (mixtureSampler V (q,z)) ∂η) :=
    Measurable.lintegral_prod_right (hf.comp (measurable_mixtureSampler V))
  have hmix : (∫⁻ x, f x ∂mixtureLaw V (μ.map (perpCoordinate V))) =
      ∫⁻ x, ∫⁻ z : V × Vᗮ, f (mixtureSampler V (perpCoordinate V x,z)) ∂η ∂μ := by
    rw [mixtureLaw,lintegral_map hf (measurable_mixtureSampler V)]
    rw [lintegral_prod (fun z : ℝ × (V × Vᗮ) => f (mixtureSampler V z))
      (hf.comp (measurable_mixtureSampler V)).aemeasurable]
    exact lintegral_map hPhi (measurable_perpCoordinate V)
  rw [hmix]
  have hm : Measurable (fun z : E × (Orthogonal V × Orthogonal Vᗮ) =>
      f (blockIso V z.2.1 z.2.2 z.1)) :=
    hf.comp ((continuous_blockIso V).comp continuous_swap).measurable
  calc
    _ = ∫⁻ z : Orthogonal V × Orthogonal Vᗮ, ∫⁻ x, f (blockIso V z.1 z.2 x) ∂μ
        ∂(orthogonalLaw (E := V)).prod (orthogonalLaw (E := Vᗮ)) := by
      simp_rw [(hinv _ _).lintegral_comp hf]
      simp
    _ = ∫⁻ x, ∫⁻ z : Orthogonal V × Orthogonal Vᗮ, f (blockIso V z.1 z.2 x)
        ∂(orthogonalLaw (E := V)).prod (orthogonalLaw (E := Vᗮ)) ∂μ :=
      (lintegral_lintegral_swap hm.aemeasurable).symm
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hunit] with x hx
      exact block_average_unit V hx hf

lemma mixtureLaw_mono (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ]
    {ρ τ : Measure ℝ} (h : ρ ≤ τ) : mixtureLaw V ρ ≤ mixtureLaw V τ :=
  Measure.map_mono (Measure.prod_mono h le_rfl) (measurable_mixtureSampler V)

lemma mixtureLaw_add (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ]
    (ρ τ : Measure ℝ) [SFinite ρ] [SFinite τ] : mixtureLaw V (ρ+τ) = mixtureLaw V ρ+mixtureLaw V τ := by
  simp only [mixtureLaw,Measure.add_prod,Measure.map_add _ _ (measurable_mixtureSampler V)]

lemma mixtureLaw_smul (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ]
    (c : ℝ≥0∞) (ρ : Measure ℝ) : mixtureLaw V (c • ρ) = c • mixtureLaw V ρ := by
  simp only [mixtureLaw,Measure.prod_smul_left,
    Measure.map_smul]

lemma mixtureLaw_domination (V : Submodule ℝ E) [Nontrivial V] [Nontrivial Vᗮ]
    (c : ℝ≥0∞) {ρ τ₀ τ₁ : Measure ℝ} [SFinite τ₀] [SFinite τ₁]
    (h : ρ ≤ c • (τ₀+τ₁)) : mixtureLaw V ρ ≤ c • (mixtureLaw V τ₀+mixtureLaw V τ₁) := by
  simpa only [mixtureLaw_smul,mixtureLaw_add] using mixtureLaw_mono V h

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent

private lemma betaRaw_eq (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) :
    betaRaw a b x = ENNReal.ofReal (beta a b) * betaPDF a b x := by
  by_cases hx : 0 < x ∧ x < 1
  · simp only [betaRaw, betaPDF, betaPDFReal, ite_eq_left hx]
    rw [← ENNReal.ofReal_mul (beta_pos ha hb).le]
    congr 1
    field_simp [(beta_pos ha hb).ne']
  · simp [betaRaw, betaPDF, betaPDFReal, hx]

private lemma lintegral_betaRaw (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫⁻ x, betaRaw a b x = ENNReal.ofReal (beta a b) := by
  simp_rw [betaRaw_eq a b _ ha hb]
  rw [lintegral_const_mul' _ _]
  · simp [lintegral_betaPDF_eq_one ha hb]
  · exact ENNReal.ofReal_ne_top

lemma beta_antitone_left {a A b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a ≤ A) :
    beta A b ≤ beta a b := by
  apply (ENNReal.ofReal_le_ofReal_iff (beta_pos ha hb).le).1
  rw [← lintegral_betaRaw A b (lt_of_lt_of_le ha h) hb, ← lintegral_betaRaw a b ha hb]
  apply lintegral_mono
  intro x
  by_cases hx : 0 < x ∧ x < 1
  · simp only [betaRaw, ite_eq_left hx]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    exact Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2.le (by linarith)
  · simp [betaRaw, hx]

lemma beta_antitone_right {a b B : ℝ} (ha : 0 < a) (hb : 0 < b) (h : b ≤ B) :
    beta a B ≤ beta a b := by
  have hcomm (u v : ℝ) : beta u v = beta v u := by unfold beta; rw [mul_comm, add_comm]
  rw [hcomm a B, hcomm a b]
  exact beta_antitone_left hb ha h

lemma betaPDFReal_domination_right_half {a A b D x : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hA : a ≤ A) (hD : A - a ≤ D)
    (hx : (1 / 2 : ℝ) ≤ x) :
    betaPDFReal a b x ≤ (2 : ℝ) ^ D * betaPDFReal A b x := by
  by_cases hx1 : x < 1
  · have hxx : 0 < x ∧ x < 1 := ⟨by linarith, hx1⟩
    simp only [betaPDFReal, ite_eq_left hxx]
    have hbeta : 1 / beta a b ≤ 1 / beta A b :=
      one_div_le_one_div_of_le (beta_pos (lt_of_lt_of_le ha hA) hb)
        (beta_antitone_left ha hb hA)
    have hp := rpow_decrease_shift hx hA hD
    have hxpow : 0 ≤ x ^ (a - 1) := Real.rpow_nonneg hxx.1.le _
    have hbpow : 0 ≤ (1 - x) ^ (b - 1) := Real.rpow_nonneg (by linarith) _
    calc
      _ ≤ ((1 / beta A b) * ((2 : ℝ) ^ D * x ^ (A - 1))) * (1 - x) ^ (b - 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hbeta hp hxpow (le_of_lt (one_div_pos.2 (beta_pos (lt_of_lt_of_le ha hA) hb)))) hbpow
      _ = _ := by ring
  · have hxx : ¬ (0 < x ∧ x < 1) := by tauto
    simp [betaPDFReal, hxx]

lemma betaPDFReal_domination_left_half {a b B D x : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hB : b ≤ B) (hD : B - b ≤ D)
    (hx : x ≤ (1 / 2 : ℝ)) :
    betaPDFReal a b x ≤ (2 : ℝ) ^ D * betaPDFReal a B x := by
  by_cases hxx : 0 < x ∧ x < 1
  · simp only [betaPDFReal, ite_eq_left hxx]
    have hbeta : 1 / beta a b ≤ 1 / beta a B :=
      one_div_le_one_div_of_le (beta_pos ha (lt_of_lt_of_le hb hB))
        (beta_antitone_right ha hb hB)
    have hp := rpow_decrease_shift (x := 1 - x) (by linarith) hB hD
    have hxpow : 0 ≤ x ^ (a - 1) := Real.rpow_nonneg hxx.1.le _
    have hbpow : 0 ≤ (1 - x) ^ (b - 1) := Real.rpow_nonneg (by linarith [hxx.2]) _
    calc
      _ ≤ ((1 / beta a B) * x ^ (a - 1)) * ((2 : ℝ) ^ D * (1 - x) ^ (B - 1)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hbeta hxpow) hp hbpow
          (mul_nonneg (le_of_lt (one_div_pos.2 (beta_pos ha (lt_of_lt_of_le hb hB)))) hxpow)
      _ = _ := by ring
  · simp [betaPDFReal, hxx]

theorem betaMeasure_two_component {a A b B D : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hA : a ≤ A) (hB : b ≤ B)
    (hAD : A - a ≤ D) (hBD : B - b ≤ D) :
    betaMeasure a b ≤ ENNReal.ofReal ((2 : ℝ) ^ D) •
      (betaMeasure A b + betaMeasure a B) := by
  have hpdf : betaPDF a b ≤ fun x => ENNReal.ofReal ((2 : ℝ) ^ D) *
      (betaPDF A b x + betaPDF a B x) := by
    intro x
    rcases le_total (1 / 2 : ℝ) x with hx | hx
    · have h := betaPDFReal_domination_right_half ha hb hA hAD hx
      have hh := ENNReal.ofReal_le_ofReal h
      rw [ENNReal.ofReal_mul (by positivity)] at hh
      exact hh.trans (mul_le_mul' le_rfl (le_add_right le_rfl))
    · have h := betaPDFReal_domination_left_half ha hb hB hBD hx
      have hh := ENNReal.ofReal_le_ofReal h
      rw [ENNReal.ofReal_mul (by positivity)] at hh
      exact hh.trans (mul_le_mul' le_rfl (le_add_left le_rfl))
  have hm : Measurable (betaPDF A b) := (measurable_betaPDFReal A b).ennreal_ofReal
  unfold betaMeasure
  rw [← withDensity_add_left hm,
    ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  exact withDensity_mono (Filter.Eventually.of_forall hpdf)

end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The full geometric two-component domination, not just a scalar-density bound. -/
theorem directionLaw_domination (V N : Submodule ℝ E) (hVN : V ≤ N)
    (hj : 1 ≤ Module.finrank ℝ V) (hjn : Module.finrank ℝ V < Module.finrank ℝ N)
    (hnD : Module.finrank ℝ N < Module.finrank ℝ E) (e : Metric.sphere (0 : V) 1) :
    directionLaw V N ≤ (2 : ℝ≥0∞)^Module.finrank ℝ E •
      (SubsphereRegression.ambientSphereLaw + latitudeLaw V e
        (((Module.finrank ℝ N : ℝ)-(Module.finrank ℝ V : ℝ))/2)
        (((Module.finrank ℝ E : ℝ)-(Module.finrank ℝ N : ℝ))/2)) := by
  have hk := V.finrank_add_finrank_orthogonal
  have hr := latitude_rank V e
  let : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (M := V) (by omega)
  let : Nontrivial Vᗮ := Module.nontrivial_of_finrank_pos (R := ℝ) (M := Vᗮ) (by omega)
  let : Nontrivial N := Module.nontrivial_of_finrank_pos (R := ℝ) (M := N) (by omega)
  let : Nontrivial (latitudeSpace V e) := Module.nontrivial_of_finrank_pos
    (R := ℝ) (M := latitudeSpace V e) (by omega)
  let a := ((Module.finrank ℝ N : ℝ)-(Module.finrank ℝ V : ℝ))/2
  let delta := ((Module.finrank ℝ E : ℝ)-(Module.finrank ℝ N : ℝ))/2
  let A := ((Module.finrank ℝ E : ℝ)-(Module.finrank ℝ V : ℝ))/2
  let b := (Module.finrank ℝ V : ℝ)/2
  let B := delta+((Module.finrank ℝ V : ℝ)-1)/2
  have hjR : (1 : ℝ) ≤ Module.finrank ℝ V := by exact_mod_cast hj
  have hjnR : (Module.finrank ℝ V : ℝ) < Module.finrank ℝ N := by exact_mod_cast hjn
  have hnDR : (Module.finrank ℝ N : ℝ)+1 ≤ Module.finrank ℝ E := by
    exact_mod_cast (Nat.add_one_le_iff.mpr hnD)
  have hdimR : (0 : ℝ) ≤ Module.finrank ℝ E := by positivity
  have ha : 0 < a := by dsimp [a]; linarith
  have hd : 0 < delta := by dsimp [delta]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hA : a ≤ A := by dsimp [a,A]; linarith
  have hB : b ≤ B := by dsimp [b,B,delta]; linarith
  have hshape : a+delta = A := by dsimp [a,delta,A]; ring
  have hAb : (Module.finrank ℝ Vᗮ : ℝ)/2 = A := by
    have hkR : (Module.finrank ℝ V : ℝ)+(Module.finrank ℝ Vᗮ : ℝ) = Module.finrank ℝ E := by
      exact_mod_cast hk
    dsimp [A]
    linarith
  have hbb : (Module.finrank ℝ Vᗮᗮ : ℝ)/2 = b := by
    have heq : Module.finrank ℝ Vᗮᗮ = Module.finrank ℝ V :=
      congrArg (fun U : Submodule ℝ E => Module.finrank ℝ U) (Submodule.orthogonal_orthogonal V)
    rw [heq]
  have huniBeta : MeasurePreserving (perpCoordinate V) SubsphereRegression.ambientSphereLaw
      (betaMeasure A b) := by
    let : Nontrivial Vᗮᗮ := by simpa using (inferInstance : Nontrivial V)
    change MeasurePreserving (fun x : E => ‖Vᗮ.orthogonalProjectionOnto x‖^2) _ _
    simpa only [hAb,hbb] using sphere_projection_beta Vᗮ
  have hlatBeta : MeasurePreserving (perpCoordinate V) (latitudeLaw V e a delta)
      (betaMeasure a B) := by
    by_cases hj1 : Module.finrank ℝ V = 1
    · have hB1 : B = delta := by dsimp [B]; rw [hj1]; norm_num
      rw [hB1]
      exact latitudeLaw_beta_one V e hj1 (by omega) ha hd
    · exact latitudeLaw_beta_gt_one V e (by omega) (hjn.trans hnD) ha hd hshape
  let : IsProbabilityMeasure (latitudeLaw V e a delta) := latitudeLaw_probability V e ha hd
  let : IsProbabilityMeasure (betaMeasure A b) := isProbabilityMeasureBeta (ha.trans_le hA) hb
  let : IsProbabilityMeasure (betaMeasure a B) := isProbabilityMeasureBeta ha (hb.trans_le hB)
  have hdir : directionLaw V N = mixtureLaw V (betaMeasure a b) := by
    rw [block_classification V (directionLaw V N) (directionLaw_unit V N)
      (directionLaw_invariant V N hVN), (directionLaw_beta V N hVN (by omega) hjn).map_eq]
  have huni : SubsphereRegression.ambientSphereLaw = mixtureLaw V (betaMeasure A b) := by
    rw [block_classification V SubsphereRegression.ambientSphereLaw
      SubsphereRegression.ambientSphereLaw_ae_norm
      (fun u w => SubsphereRegression.ambientSphereLaw_isometry (blockIso V u w)),huniBeta.map_eq]
  have hlat : latitudeLaw V e a delta = mixtureLaw V (betaMeasure a B) := by
    rw [block_classification V (latitudeLaw V e a delta) (latitudeLaw_unit V e ha hd)
      (latitudeLaw_invariant V e ha hd),hlatBeta.map_eq]
  have hscalar : betaMeasure a b ≤ (2 : ℝ≥0∞)^Module.finrank ℝ E •
      (betaMeasure A b+betaMeasure a B) := by
    have hAD : A-a ≤ (Module.finrank ℝ E : ℝ) := by dsimp [A,a]; linarith
    have hBD : B-b ≤ (Module.finrank ℝ E : ℝ) := by dsimp [B,b,delta]; linarith
    have h := SubsphereCurrent.betaMeasure_two_component ha hb hA hB hAD hBD
    simpa only [Real.rpow_natCast, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat] using h
  change directionLaw V N ≤ _ • (SubsphereRegression.ambientSphereLaw + latitudeLaw V e a delta)
  rw [hdir,huni,hlat]
  exact mixtureLaw_domination V _ hscalar

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory Set
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

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

end SubsphereCurrent.Mixture
end
end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Mixture
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.Mixture.directionLaw_domination := @_root_.OAI.SubsphereCurrent.Mixture.directionLaw_domination
