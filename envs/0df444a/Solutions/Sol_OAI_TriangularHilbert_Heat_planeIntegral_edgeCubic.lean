-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.planeIntegral_edgeCubic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:59:51.048598+00:00
-- url     : https://prove2.me/submissions/b780491c-8c33-4a48-8942-60f8f31057e3

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/MassPlane.lean:L68-L81
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.planeIntegral_edgeCubic. The node keeps its source
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

-- ---- from OAI.Analysis.TriangularHilbert.MeshMass ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology BigOperators
noncomputable section

lemma integral_density {σ : ℝ} (hσ : 0 < σ) : (∫ t, density σ t) = 1 := by
  rw [density_eq_gaussianPDFReal hσ.le]
  apply ProbabilityTheory.integral_gaussianPDFReal_eq_one
  intro he
  have he' : σ = 0 := congrArg (fun r : NNReal => (r : ℝ)) he
  exact hσ.ne' he'

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

lemma integral_chart_eq (i j : Three) (d : ℝ) (f : (Three → ℝ) → ℝ) :
    (∫ z : ℝ × ℝ, f (chart i d z)) = ∫ z : ℝ × ℝ, f (chart j d z) := by
  have hi k : (∫ z : ℝ × ℝ, f (chart k d z)) = ∫ z : ℝ × ℝ, f (chart 2 d z) := by
    simp_rw [chartChange_eq k d]
    exact (chartChange_preserving k d).integral_comp (chartChange k d).measurableEmbedding
      (fun z : ℝ × ℝ => f (chart 2 d z))
  exact (hi i).trans (hi j).symm

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.PlaneIntegral ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

lemma planeIntegral_eq (f : (Three → ℝ) → ℝ) (i : Three) (d : ℝ) :
    planeIntegral f d = ∫ z : ℝ × ℝ, f (chart i d z) := integral_chart_eq 2 i d f

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

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

lemma integral_weight_center (h u : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (∫ p, weight h u p σ) = h := by
  unfold weight
  rw [integral_const_mul,integral_sub_left_eq_self,integral_density hσ,mul_one]

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

lemma integral_weight_pair (h a b d : ℝ) (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v : Three) :
    planeIntegral (fun p => weight h a (p v) (σ v)*weight h b (p (v+1)) (σ (v+1))) d = h^2 := by
  rw [planeIntegral_eq _ (v+2)]
  change (∫ z : ℝ×ℝ, weight h a (chart (v+2) d z v) (σ v)*weight h b (chart (v+2) d z (v+1)) (σ (v+1)) ∂volume.prod volume) = h^2
  have hp (a b σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ) :
      (∫ z : ℝ×ℝ, weight h a z.1 σ * weight h b z.2 τ ∂volume.prod volume) = h^2 := by
    rw [integral_prod_mul (fun p => weight h a p σ) (fun p => weight h b p τ),
      integral_weight_center h a hσ,integral_weight_center h b hτ,pow_two]
  fin_cases v
  · simpa [chart] using hp a b (σ 0) (σ 1) (hσ 0) (hσ 1)
  · simpa [chart] using hp a b (σ 1) (σ 2) (hσ 1) (hσ 2)
  · simpa [chart,mul_comm] using hp b a (σ 0) (σ 2) (hσ 0) (hσ 2)

variable {ι : Type uι} [Fintype ι]

lemma planeIntegral_edgeCubic (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (d : ℝ)
    (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v : Three) :
    planeIntegral (fun p => edgeCubic A h u p σ v) d = ∑ i, ∑ j, h^2 * ‖A v i j‖^3 := by
  unfold planeIntegral edgeCubic heatWeights
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (weight_pair_integrable h (u i) (u j) d σ hσ v 2).const_mul _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (weight_pair_integrable h (u i) (u j) d σ hσ v 2).const_mul _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  change ‖A v i j‖^3 * planeIntegral (fun p => weight h (u i) (p v) (σ v)*weight h (u j) (p (v+1)) (σ (v+1))) d = _
  rw [integral_weight_pair h (u i) (u j) d σ hσ v,mul_comm]
end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.Heat.planeIntegral_edgeCubic.{uι} := @_root_.OAI.TriangularHilbert.Heat.planeIntegral_edgeCubic.{uι}
