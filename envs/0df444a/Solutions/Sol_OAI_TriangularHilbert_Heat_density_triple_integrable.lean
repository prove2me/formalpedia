-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.density_triple_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:01:34.557933+00:00
-- url     : https://prove2.me/submissions/0f145ca2-233f-4ba0-bf5c-39f07fe31569

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/GaussianTriple.lean:L10-L24
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.density_triple_integrable. The node keeps its source
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

lemma continuous_density (σ : ℝ) : Continuous (density σ) := by
  unfold density
  fun_prop

end
end TriangularHilbert.Heat
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

-- ---- from OAI.Analysis.TriangularHilbert.GaussianTriple ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

lemma density_triple_integrable {s t v : ℝ} (hs : 0 < s) (ht : 0 < t) (hv : 0 < v) (a b c : ℝ) :
    Integrable (fun z : ℝ×ℝ => density s (a-z.1)*density t (b-z.2)*density v (c+z.1+z.2)) := by
  have hst : Integrable (fun z : ℝ×ℝ => density s (a-z.1)*density t (b-z.2)) := by
    exact ((volume.measurePreserving_sub_left a).integrable_comp_of_integrable (density_integrable hs.le)).mul_prod
      ((volume.measurePreserving_sub_left b).integrable_comp_of_integrable (density_integrable ht.le))
  apply (hst.mul_const (density v 0)).mono'
  · have hc : Continuous (fun z : ℝ×ℝ => density s (a-z.1)*density t (b-z.2)*density v (c+z.1+z.2)) :=
      (((continuous_density s).comp (continuous_const.sub continuous_fst)).mul
        ((continuous_density t).comp (continuous_const.sub continuous_snd))).mul
          ((continuous_density v).comp ((continuous_const.add continuous_fst).add continuous_snd))
    exact hc.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (mul_nonneg (density_nonneg hs.le _) (density_nonneg ht.le _)) (density_nonneg hv.le _))]
    exact mul_le_mul_of_nonneg_left (density_le_zero v _) (mul_nonneg (density_nonneg hs.le _) (density_nonneg ht.le _))

end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory


theorem solution : type_of% @_root_.OAI.TriangularHilbert.Heat.density_triple_integrable := @_root_.OAI.TriangularHilbert.Heat.density_triple_integrable
