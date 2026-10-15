-- Prove2me | solution 1 for OAI.IndependentProducts.norm_child_difference
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:01:59.181872+00:00
-- url     : https://prove2.me/submissions/79f519a6-e7d6-4455-9a27-fc9398cc5a44

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/PathMoments.lean:L265-L287
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.norm_child_difference. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Theorems.Thm_OAI_IndependentProducts_pathProduct_child

-- ---- from OAI.Analysis.ProductSpaces.PathMoments ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι

namespace IndependentProducts
section CoordinateProducts

lemma pathProduct_eq_prod_pathEdges (v : Vertex) (ω : Sample) :
    pathProduct v ω = ∏ e ∈ pathEdges v, ω e := by
  simp [pathEdges, pathProduct]

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma integral_coordinates_prod {ι : Type uι} [Fintype ι]
    (e : ι → Edge) (he : Function.Injective e) (f : ι → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) :
    (∫ ω : Sample, ∏ i, f i (ω (e i)) ∂productMeasure μ) = ∏ i, ∫ w, f i w ∂μ := by
  let hmp := measurePreserving_coordinates μ e he
  have hg : AEStronglyMeasurable (fun x : ι → ℝ => ∏ i, f i (x i))
      ((productMeasure μ).map (fun ω : Sample => fun i => ω (e i))) := by
    exact (Finset.measurable_prod _ (fun i _ => (hf i).comp (measurable_pi_apply i))).aestronglyMeasurable
  rw [← integral_map hmp.measurable.aemeasurable hg, hmp.map_eq,
    integral_fintype_prod_eq_prod]

lemma integral_pathProduct (v : Vertex) :
    (∫ ω, pathProduct v ω ∂productMeasure μ) = (∫ w : ℝ, w ∂μ) ^ v.length := by
  have hi := integral_coordinates_prod μ (pathPrefix v) (pathPrefix_injective v)
    (fun _ w => w) (fun _ => measurable_id)
  simpa [pathProduct] using hi

lemma pathProduct_pos (hpos : ∀ᵐ w ∂μ, (0 : ℝ) < w) (v : Vertex) :
    ∀ᵐ ω ∂productMeasure μ, 0 < pathProduct v ω := by
  have hcoord : ∀ j : Fin v.length, ∀ᵐ ω ∂productMeasure μ,
      0 < ω (pathPrefix v j) := fun j =>
    (measurePreserving_eval_infinitePi (fun _ : Edge => μ) (pathPrefix v j)).quasiMeasurePreserving.ae hpos
  filter_upwards [ae_all_iff.mpr hcoord] with ω hω
  exact Finset.prod_pos (fun j _ => hω j)

end CoordinateProducts
end IndependentProducts

namespace IndependentProducts

lemma childEdge_not_mem_pathEdges (v : Vertex) (n : ℕ) : childEdge v n ∉ pathEdges v := by
  intro h
  obtain ⟨j, _, hj⟩ := Finset.mem_map.mp h
  have he := congrArg (fun e : Edge => e.val.length) hj
  simp only [Function.Embedding.coeFn_mk, pathPrefix_length, childEdge, child_length] at he
  omega

section ChildMoments
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma indepFun_path_coordinate (v : Vertex) (e : Edge) (he : e ∉ pathEdges v) :
    IndepFun (pathProduct v) (fun ω : Sample => ω e) (productMeasure μ) := by
  have hi : iIndepFun (fun e : Edge => fun ω : Sample => ω e) (productMeasure μ) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have hh := hi.indepFun_finsetProd_of_notMem (fun e => measurable_pi_apply e) he
  have heq : (∏ j ∈ pathEdges v, fun ω : Sample => ω j) = pathProduct v := by
    funext ω
    simp only [Finset.prod_apply, ← pathProduct_eq_prod_pathEdges]
  rwa [heq] at hh

lemma integral_coordinate (e : Edge) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ ω : Sample, f (ω e) ∂productMeasure μ) = ∫ w, f w ∂μ := by
  have hm : MeasurePreserving (fun ω : Sample => ω e) (productMeasure μ) μ :=
    measurePreserving_eval_infinitePi (fun _ : Edge => μ) e
  rw [← integral_map hm.measurable.aemeasurable hf.aestronglyMeasurable, hm.map_eq]

lemma integral_path_mul_coordinate (v : Vertex) (e : Edge) (he : e ∉ pathEdges v)
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g) :
    (∫ ω : Sample, f (pathProduct v ω) * g (ω e) ∂productMeasure μ) =
      (∫ ω, f (pathProduct v ω) ∂productMeasure μ) * ∫ w, g w ∂μ := by
  rw [(indepFun_path_coordinate μ v e he).integral_fun_comp_mul_comp
    (measurable_pathProduct v).aemeasurable (measurable_pi_apply e).aemeasurable
    hf.aestronglyMeasurable hg.aestronglyMeasurable, integral_coordinate μ e g hg]

lemma norm_child_difference (h₂ : MemLp (fun w : ℝ => w) 2 μ)
    (hpos : ∀ᵐ w ∂μ, (0 : ℝ) < w) (hmean : ∫ w : ℝ, w ∂μ = 1) (v : Vertex) (n : ℕ) :
    ‖pathVector μ h₂ (child v n) - pathVector μ h₂ v‖ = ∫ w : ℝ, |w - 1| ∂μ := by
  change ‖pathL1 μ h₂ (child v n) - pathL1 μ h₂ v‖ = _
  rw [L1.norm_eq_integral_norm]
  calc
    (∫ ω, ‖(pathL1 μ h₂ (child v n) - pathL1 μ h₂ v) ω‖ ∂productMeasure μ) =
        ∫ ω, pathProduct v ω * |ω (childEdge v n) - 1| ∂productMeasure μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (pathL1 μ h₂ (child v n)) (pathL1 μ h₂ v),
        pathL1_ae μ h₂ (child v n), pathL1_ae μ h₂ v, pathProduct_pos μ hpos v] with ω hs hc hp hpos
      rw [hs]
      change ‖pathL1 μ h₂ (child v n) ω - pathL1 μ h₂ v ω‖ = _
      rw [hc, hp, pathProduct_child, ← mul_sub_one, Real.norm_eq_abs,
        abs_mul, abs_of_pos hpos]
    _ = 1 * ∫ w : ℝ, |w - 1| ∂μ := by
      have hh := integral_path_mul_coordinate μ v _ (childEdge_not_mem_pathEdges v n)
        id (fun w => |w - 1|) measurable_id ((measurable_id.sub_const 1).abs)
      dsimp at hh
      rw [hh]
      congr 1
      rw [integral_pathProduct, hmean, one_pow]
    _ = _ := one_mul _

end ChildMoments
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uι
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

theorem solution (h₂ : MemLp (fun w : ℝ => w) 2 μ)
    (hpos : ∀ᵐ w ∂μ, (0 : ℝ) < w) (hmean : ∫ w : ℝ, w ∂μ = 1) (v : Vertex) (n : ℕ) :
    ‖pathVector μ h₂ (child v n) - pathVector μ h₂ v‖ = ∫ w : ℝ, |w - 1| ∂μ := by
  first
    | exact OAI.IndependentProducts.norm_child_difference h₂ hpos hmean v n
    | exact OAI.IndependentProducts.norm_child_difference μ h₂ hpos hmean v n
    | exact OAI.IndependentProducts.norm_child_difference
    | (apply OAI.IndependentProducts.norm_child_difference <;> assumption)
    | (intros; apply OAI.IndependentProducts.norm_child_difference <;> assumption)
