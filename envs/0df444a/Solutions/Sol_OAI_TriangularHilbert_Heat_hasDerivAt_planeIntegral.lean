-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.hasDerivAt_planeIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:44:52.128132+00:00
-- url     : https://prove2.me/submissions/4bd5dae0-1e3e-42bf-8b21-067cf79751a0

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/PlaneIntegral.lean:L35-L52
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.hasDerivAt_planeIntegral. The node keeps its source
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

lemma chart_hasDerivAt (i : Three) (d : ℝ) (z : ℝ × ℝ) :
    HasDerivAt (fun e => chart i e z i) 1 d := by
  have he : (fun e => chart i e z i) = (fun e => e-z.1-z.2) := by
    funext e
    fin_cases i <;> simp [chart]
  rw [he]
  exact ((hasDerivAt_id d).sub_const z.1).sub_const z.2

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

lemma measurable_chart (i : Three) (d : ℝ) : Measurable (chart i d) :=
  ((chart_continuous i).comp (continuous_const.prodMk continuous_id)).measurable

lemma hasDerivAt_chart_of_center {f : (Three → ℝ) → ℝ} {g : (Three → ℝ) → ℝ}
    (i : Three) (d : ℝ) (z : ℝ × ℝ)
    (h : ∀ p, HasDerivAt (fun t => f (Function.update p i t)) (g p) (p i)) :
    HasDerivAt (fun e => f (chart i e z)) (g (chart i d z)) d := by
  have hd := (h (chart i d z)).comp d (chart_hasDerivAt i d z)
  simp only [mul_one] at hd
  apply hd.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro e
  apply congrArg f
  ext j
  fin_cases i <;> fin_cases j <;> simp [chart,Function.update]

lemma planeIntegral_eq (f : (Three → ℝ) → ℝ) (i : Three) (d : ℝ) :
    planeIntegral f d = ∫ z : ℝ × ℝ, f (chart i d z) := integral_chart_eq 2 i d f

lemma hasDerivAt_planeIntegral {f g : (Three → ℝ) → ℝ} {B : (ℝ × ℝ) → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hB : Integrable B)
    (i : Three) (d : ℝ)
    (hb0 : ∀ z, ‖f (chart i d z)‖ ≤ B z)
    (hb : ∀ e ∈ Set.Ioo (d-1) (d+1), ∀ z, ‖g (chart i e z)‖ ≤ B z)
    (hd : ∀ p, HasDerivAt (fun t => f (Function.update p i t)) (g p) (p i)) :
    HasDerivAt (planeIntegral f) (planeIntegral g d) d := by
  have hs : Set.Ioo (d-1) (d+1) ∈ 𝓝 d := Ioo_mem_nhds (by linarith) (by linarith)
  have hint : Integrable (fun z => f (chart i d z)) :=
    hB.mono' (hf.comp (measurable_chart i d)).aestronglyMeasurable (Eventually.of_forall hb0)
  have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun e z => f (chart i e z))
    (F' := fun e z => g (chart i e z)) hs
    (Eventually.of_forall (fun e => (hf.comp (measurable_chart i e)).aestronglyMeasurable)) hint
    (hg.comp (measurable_chart i d)).aestronglyMeasurable
    (Eventually.of_forall (fun z e he => hb e he z)) hB
    (Eventually.of_forall (fun z e _ => hasDerivAt_chart_of_center i e z hd))).2
  rw [← planeIntegral_eq g i d] at hh
  exact hh.congr_of_eventuallyEq (Eventually.of_forall (fun e => planeIntegral_eq f i e))

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder


theorem solution : type_of% @_root_.OAI.TriangularHilbert.Heat.hasDerivAt_planeIntegral := @_root_.OAI.TriangularHilbert.Heat.hasDerivAt_planeIntegral
