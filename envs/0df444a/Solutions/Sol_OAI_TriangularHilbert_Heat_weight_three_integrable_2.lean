-- Prove2me | solution 2 for OAI.TriangularHilbert.Heat.weight_three_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:18:30.66041+00:00
-- url     : https://prove2.me/submissions/3a7fb5b9-a4f4-4a5c-8b68-399a9128add9

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/GaussianExpectation.lean:L10-L28
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.weight_three_integrable. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump

-- ---- from OAI.Analysis.TriangularHilbert.Gaussian ----
namespace OAI

section

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TriangularHilbert.Heat

theorem density_eq_gaussianPDFReal {σ : ℝ} (hσ : 0 ≤ σ) :
    density σ = ProbabilityTheory.gaussianPDFReal 0 ⟨σ, hσ⟩ := by
  ext t
  change (Real.sqrt (2 * Real.pi * σ))⁻¹ * Real.exp (-t^2 / (2*σ)) =
    (Real.sqrt (2 * Real.pi * σ))⁻¹ * Real.exp (-(t-0)^2 / (2*σ))
  rw [sub_zero]

theorem density_integrable {σ : ℝ} (hσ : 0 ≤ σ) : Integrable (density σ) := by
  rw [density_eq_gaussianPDFReal hσ]
  exact ProbabilityTheory.integrable_gaussianPDFReal 0 _

end TriangularHilbert.Heat
end
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.GaussianConvolution ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

lemma density_le_zero (σ x : ℝ) : density σ x ≤ density σ 0 := by
  by_cases hs : 0 < σ
  · unfold density
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    simp only [zero_pow (by decide : 2 ≠ 0),neg_zero,zero_div]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) (by positivity)
  · have he : Real.sqrt (2*Real.pi*σ) = 0 := Real.sqrt_eq_zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt hs))
    simp [density,he]

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.GaussianGram ----
namespace OAI

universe uι

section

namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma weight_pos {h σ : ℝ} (hh : 0 < h) (hσ : 0 < σ) (u p : ℝ) :
    0 < weight h u p σ := mul_pos hh (density_pos hσ _)

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.PlaneChart ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
open MatrixEnergy
noncomputable section

lemma chart_continuous (i : Three) : Continuous (fun q : ℝ × (ℝ × ℝ) => chart i q.1 q.2) := by
  unfold chart
  split_ifs <;> fun_prop

lemma chartReflection_preserving (d : ℝ) : MeasurePreserving (chartReflection d) := by
  exact (MeasurePreserving.id volume).skew_product
    (g := fun x y : ℝ => d-x-y) (by fun_prop)
    (Filter.Eventually.of_forall (fun x => (volume.measurePreserving_sub_left (d-x)).map_eq))

lemma swap_preserving : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) :=
  ⟨measurable_swap, Measure.prod_swap⟩

lemma chartChange_preserving (i : Three) (d : ℝ) : MeasurePreserving (chartChange i d) := by
  unfold chartChange
  split_ifs
  · exact swap_preserving.comp (chartReflection_preserving d)
  · exact chartReflection_preserving d
  · exact MeasurePreserving.id volume

lemma chartChange_eq (i : Three) (d : ℝ) (z : ℝ × ℝ) :
    chart i d z = chart 2 d (chartChange i d z) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [chart, chartChange, chartReflection]
  all_goals ring

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.MassPlane ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

lemma weight_integrable_center (h u σ : ℝ) (hσ : 0 ≤ σ) :
    Integrable (fun p => weight h u p σ) := by
  exact ((volume.measurePreserving_sub_left u).integrable_comp_of_integrable (density_integrable hσ)).const_mul h

lemma chart_integrable_iff (f : (Three → ℝ) → ℝ) (i j : Three) (d : ℝ) :
    Integrable (fun z : ℝ×ℝ => f (chart i d z)) ↔
      Integrable (fun z : ℝ×ℝ => f (chart j d z)) := by
  have hi k : Integrable (fun z : ℝ×ℝ => f (chart k d z)) ↔
      Integrable (fun z : ℝ×ℝ => f (chart 2 d z)) := by
    simp_rw [chartChange_eq k d]
    exact (chartChange_preserving k d).integrable_comp_emb (chartChange k d).measurableEmbedding (g := fun z : ℝ×ℝ => f (chart 2 d z))
  exact (hi i).trans (hi j).symm

lemma weight_pair_integrable (h a b d : ℝ) (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v k : Three) :
    Integrable (fun z : ℝ×ℝ => weight h a (chart k d z v) (σ v) *
      weight h b (chart k d z (v+1)) (σ (v+1))) := by
  apply (chart_integrable_iff (fun p => weight h a (p v) (σ v)*weight h b (p (v+1)) (σ (v+1))) (v+2) k d).mp
  change Integrable (fun z : ℝ×ℝ => weight h a (chart (v+2) d z v) (σ v)*weight h b (chart (v+2) d z (v+1)) (σ (v+1))) (volume.prod volume)
  fin_cases v
  · simpa [chart] using (weight_integrable_center h a (σ 0) (hσ 0).le).mul_prod
      (weight_integrable_center h b (σ 1) (hσ 1).le)
  · simpa [chart] using (weight_integrable_center h a (σ 1) (hσ 1).le).mul_prod
      (weight_integrable_center h b (σ 2) (hσ 2).le)
  · simpa [chart,mul_comm] using (weight_integrable_center h b (σ 0) (hσ 0).le).mul_prod
      (weight_integrable_center h a (σ 2) (hσ 2).le)

variable {ι : Type uι} [Fintype ι]

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.JointHeat ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uE

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_weight_param {E : Type uE} [TopologicalSpace E] (h u : ℝ)
    {p σ : E → ℝ} (hp : Continuous p) (hσ : Continuous σ) (hpos : ∀ t, 0 < σ t) :
    Continuous (fun t => weight h u (p t) (σ t)) := by
  unfold weight density
  have hden : ∀ t, Real.sqrt (2*Real.pi*σ t) ≠ 0 := fun t => (Real.sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) Real.pi_pos) (hpos t))).ne'
  apply continuous_const.mul
  apply Continuous.mul
  · exact (Real.continuous_sqrt.comp (continuous_const.mul hσ)).inv₀ hden
  · apply Real.continuous_exp.comp
    exact ((continuous_const.sub hp).pow 2 |>.neg).div (continuous_const.mul hσ) (fun t => (mul_pos (by norm_num) (hpos t)).ne')

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.GaussianExpectation ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
noncomputable section

lemma weight_three_integrable {h : ℝ} (hh : 0 < h) (a b c d : ℝ)
    (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v : Three) :
    Integrable (fun z : ℝ×ℝ => weight h a (chart 2 d z 0) (σ 0)*
      weight h b (chart 2 d z 1) (σ 1)*weight h c (chart 2 d z v) (σ v)) := by
  have hi := weight_pair_integrable h a b d σ hσ 0 2
  have he : (0:Three)+1=1 := by decide
  rw [he] at hi
  apply (hi.mul_const (h*density (σ v) 0)).mono'
  · have hc (k : Three) : Continuous (fun z : ℝ×ℝ => chart 2 d z k) :=
      (continuous_apply k).comp ((chart_continuous 2).comp (continuous_const.prodMk continuous_id))
    exact ((continuous_weight_param h a (hc 0) continuous_const (fun _ => hσ 0)).mul
      (continuous_weight_param h b (hc 1) continuous_const (fun _ => hσ 1)) |>.mul
      (continuous_weight_param h c (hc v) continuous_const (fun _ => hσ v))).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (mul_nonneg
      (weight_pos hh (hσ 0) _ _).le (weight_pos hh (hσ 1) _ _).le) (weight_pos hh (hσ v) _ _).le)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (density_le_zero (σ v) _) hh.le)
      (mul_nonneg (weight_pos hh (hσ 0) _ _).le (weight_pos hh (hσ 1) _ _).le)

end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory


theorem solution : type_of% @_root_.OAI.TriangularHilbert.Heat.weight_three_integrable := @_root_.OAI.TriangularHilbert.Heat.weight_three_integrable
