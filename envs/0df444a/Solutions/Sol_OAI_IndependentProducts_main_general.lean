-- Prove2me | solution 1 for OAI.IndependentProducts.main_general
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:49:09.782854+00:00
-- url     : https://prove2.me/submissions/270bb5c7-6e96-4aed-be34-3bbff87c1e0c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/WeakNullity.lean:L205-L217
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.IndependentProducts.main_general.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_IndependentProducts_main_general) verbatim and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Theorems.Thm_OAI_IndependentProducts_bounded_tree_no_equivalent_auc
import Theorems.Thm_OAI_IndependentProducts_indepFun_finset_coordinates
import Theorems.Thm_OAI_IndependentProducts_norm_child_difference
import Theorems.Thm_OAI_IndependentProducts_pathProduct_child

-- ---- from OAI.Analysis.ProductSpaces.TreeObstruction ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uX

namespace IndependentProducts

section AbstractObstruction

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma weaklyNull_tendsto_finiteDimensional [FiniteDimensional ℝ X]
    {u : ℕ → X} (hu : WeaklyNull u) : Tendsto u atTop (𝓝 0) := by
  let e := (Module.finBasis ℝ X).equivFunL
  have he : Tendsto (fun n => e (u n)) atTop (𝓝 (e 0)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa using hu ((ContinuousLinearMap.proj i).comp e.toContinuousLinearMap)
  have h := (e.symm.continuous.tendsto (e 0)).comp he
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply, map_zero] using h

end AbstractObstruction
end IndependentProducts

namespace IndependentProducts
section RadialGrowth
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

end RadialGrowth
end IndependentProducts

namespace IndependentProducts
section TreeObstruction
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma not_finiteDimensional_of_weaklyNull_fixed_norm {u : ℕ → X}
    (hu : WeaklyNull u) {ρ : ℝ} (hρ : 0 < ρ) (hsize : ∀ n, ‖u n‖ = ρ) :
    ¬ FiniteDimensional ℝ X := by
  intro hfin
  let := hfin
  have hn := (weaklyNull_tendsto_finiteDimensional hu).norm
  simp only [norm_zero] at hn
  obtain ⟨n, hn⟩ := (hn.eventually (gt_mem_nhds hρ)).exists
  simp only [hsize n, lt_self_iff_false] at hn

end TreeObstruction
end IndependentProducts

end

end OAI

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

lemma norm_pathVector (h₂ : MemLp (fun w : ℝ => w) 2 μ)
    (hpos : ∀ᵐ w ∂μ, (0 : ℝ) < w) (hmean : ∫ w : ℝ, w ∂μ = 1) (v : Vertex) :
    ‖pathVector μ h₂ v‖ = 1 := by
  change ‖pathL1 μ h₂ v‖ = 1
  rw [L1.norm_eq_integral_norm]
  calc
    (∫ ω, ‖pathL1 μ h₂ v ω‖ ∂productMeasure μ) = ∫ ω, pathProduct v ω ∂productMeasure μ := by
      apply integral_congr_ae
      filter_upwards [pathL1_ae μ h₂ v, pathProduct_pos μ hpos v] with ω he hp
      rw [he, Real.norm_eq_abs, abs_of_pos hp]
    _ = 1 := by rw [integral_pathProduct, hmean, one_pow]

end CoordinateProducts
end IndependentProducts

namespace IndependentProducts

lemma childEdge_injective (v : Vertex) : Function.Injective (childEdge v) := by
  intro m n h
  have h' := congrArg Subtype.val h
  change v ++ [_] = v ++ [_] at h'
  have hh := List.cons.inj (List.append_cancel_left h')
  have := congrArg (fun x : ℕ+ => x.val) hh.1
  dsimp at this
  omega

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

lemma mean_abs_deviation_pos (h₂ : MemLp (fun w : ℝ => w) 2 μ)
    (hnot : ∀ c : ℝ, ¬ (∀ᵐ w ∂μ, w = c)) : 0 < ∫ w : ℝ, |w - 1| ∂μ := by
  have hi : Integrable (fun w : ℝ => |w - 1|) μ :=
    ((h₂.integrable (by norm_num)).sub (integrable_const 1)).abs
  have hnonneg : 0 ≤ ∫ w : ℝ, |w - 1| ∂μ := integral_nonneg (fun _ => abs_nonneg _)
  apply lt_of_le_of_ne hnonneg
  intro he
  have hz := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all μ (fun w => abs_nonneg (w - 1))) hi).mp he.symm
  apply hnot 1
  filter_upwards [hz] with w hw
  exact sub_eq_zero.mp (abs_eq_zero.mp hw)

end ChildMoments
end IndependentProducts

end

end OAI

-- ---- from OAI.Analysis.ProductSpaces.WeakNullity ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uH uα

namespace IndependentProducts
section HilbertTools

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma weaklyNull_of_orthogonal_fixed_norm (u : ℕ → H) (c : ℝ) (hc : 0 < c)
    (hn : ∀ n, ‖u n‖ = c) (hi : Pairwise (fun n m => inner ℝ (u n) (u m) = 0)) :
    WeaklyNull u := by
  let w : ℕ → H := fun n => c⁻¹ • u n
  have hw : Orthonormal ℝ w := by
    constructor
    · intro n
      simp [w, norm_smul, hn, Real.norm_eq_abs, abs_of_pos hc, hc.ne']
    · intro n m hnm
      simp [w, inner_smul_left, inner_smul_right, hi hnm]
  intro f
  let y := (InnerProductSpace.toDual ℝ H).symm f
  have hs := (hw.inner_products_summable y).tendsto_atTop_zero
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  have hnorm : Tendsto (fun n => ‖f (w n)‖) atTop (𝓝 0) := by
    have he : ∀ n, inner ℝ (w n) y = f (w n) := fun n => by
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero, he] using hsqrt
  have hfw := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have heq : (fun n => f (u n)) = (fun n => c * f (w n)) := by
    funext n
    rw [← smul_eq_mul, ← map_smul]
    congr 1
    dsimp [w]
    rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  rw [heq]
  simpa using hfw.const_mul c

variable {α : Type uα} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]

lemma l2ToL1_coe (f : Lp ℝ 2 ν) : (l2ToL1 ν f : α → ℝ) = f := rfl

lemma norm_l2ToL1_le (f : Lp ℝ 2 ν) : ‖l2ToL1 ν f‖ ≤ ‖f‖ := by
  simp only [Lp.norm_def, l2ToL1_coe]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (Lp.aestronglyMeasurable f))

end HilbertTools

section ChildL2
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]
variable (h₂ : MemLp (fun w : ℝ => w) 2 μ)

lemma childIncrementL2_ae (v : Vertex) (n : ℕ) :
    (childIncrementL2 μ h₂ v n : Sample → ℝ) =ᵐ[productMeasure μ]
      fun ω => pathProduct v ω * (ω (childEdge v n) - 1) := by
  filter_upwards [Lp.coeFn_sub ((pathProduct_memLp μ h₂ (child v n)).toLp _)
    ((pathProduct_memLp μ h₂ v).toLp _), (pathProduct_memLp μ h₂ (child v n)).coeFn_toLp,
    (pathProduct_memLp μ h₂ v).coeFn_toLp] with ω hs hc hp
  unfold childIncrementL2
  rw [hs]
  change ((pathProduct_memLp μ h₂ (child v n)).toLp _) ω -
    ((pathProduct_memLp μ h₂ v).toLp _) ω = _
  rw [hc, hp, pathProduct_child]
  ring

lemma l2ToL1_childIncrement (v : Vertex) (n : ℕ) :
    l2ToL1 (productMeasure μ) (childIncrementL2 μ h₂ v n) =
      pathL1 μ h₂ (child v n) - pathL1 μ h₂ v := by
  apply Lp.ext
  filter_upwards [childIncrementL2_ae μ h₂ v n,
    Lp.coeFn_sub (pathL1 μ h₂ (child v n)) (pathL1 μ h₂ v),
    pathL1_ae μ h₂ (child v n), pathL1_ae μ h₂ v] with ω hi hs hc hp
  rw [l2ToL1_coe, hi, hs]
  change _ = pathL1 μ h₂ (child v n) ω - pathL1 μ h₂ v ω
  rw [hc, hp, pathProduct_child]
  ring

lemma childIncrementL2_norm_constant (v : Vertex) (n : ℕ) :
    ‖childIncrementL2 μ h₂ v n‖ = ‖childIncrementL2 μ h₂ v 0‖ := by
  have hi : ∀ k, inner ℝ (childIncrementL2 μ h₂ v k) (childIncrementL2 μ h₂ v k) =
      (∫ ω, pathProduct v ω ^ 2 ∂productMeasure μ) * ∫ w : ℝ, (w - 1) ^ 2 ∂μ := by
    intro k
    rw [L2.inner_def]
    calc
      (∫ ω, inner ℝ (childIncrementL2 μ h₂ v k ω) (childIncrementL2 μ h₂ v k ω) ∂productMeasure μ) =
          ∫ ω, pathProduct v ω ^ 2 * (ω (childEdge v k) - 1) ^ 2 ∂productMeasure μ := by
        apply integral_congr_ae
        filter_upwards [childIncrementL2_ae μ h₂ v k] with ω hω
        rw [hω, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
        ring
      _ = _ := integral_path_mul_coordinate μ v _ (childEdge_not_mem_pathEdges v k)
        (fun x => x ^ 2) (fun x => (x - 1) ^ 2) (measurable_id.pow_const 2)
        ((measurable_id.sub_const 1).pow_const 2)
  have he := (hi n).trans (hi 0).symm
  simp only [real_inner_self_eq_norm_sq] at he
  nlinarith [norm_nonneg (childIncrementL2 μ h₂ v n), norm_nonneg (childIncrementL2 μ h₂ v 0)]

lemma indepFun_pathSquare_mul_child (v : Vertex) {n m : ℕ} (hnm : n ≠ m) :
    IndepFun (fun ω : Sample => pathProduct v ω ^ 2 * (ω (childEdge v n) - 1))
      (fun ω : Sample => ω (childEdge v m)) (productMeasure μ) := by
  classical
  let f : Edge → ℝ → ℝ := fun e w => if e = childEdge v n then w - 1 else w ^ 2
  have hf : ∀ e, Measurable (f e) := fun e => by
    dsimp [f]
    split_ifs
    · exact measurable_id.sub_const 1
    · exact measurable_id.pow_const 2
  have hnot : childEdge v m ∉ insert (childEdge v n) (pathEdges v) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun he => hnm ((childEdge_injective v he).symm), childEdge_not_mem_pathEdges v m⟩
  have hi := indepFun_finset_coordinates μ (insert (childEdge v n) (pathEdges v)) f hf
    (childEdge v m) hnot
  have he : (fun ω : Sample => ∏ i ∈ insert (childEdge v n) (pathEdges v), f i (ω i)) =
      (fun ω => pathProduct v ω ^ 2 * (ω (childEdge v n) - 1)) := by
    funext ω
    rw [Finset.prod_insert (childEdge_not_mem_pathEdges v n)]
    have hp : (∏ i ∈ pathEdges v, f i (ω i)) = pathProduct v ω ^ 2 := by
      rw [pathProduct_eq_prod_pathEdges, ← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro i hi
      have hne : i ≠ childEdge v n := fun h => childEdge_not_mem_pathEdges v n (h ▸ hi)
      simp [f, hne]
    simp only [f, ite_eq_left rfl, hp]
    ring
  rwa [he] at hi

lemma childIncrementL2_orthogonal (hmean : ∫ w : ℝ, w ∂μ = 1) (v : Vertex) :
    Pairwise (fun n m => inner ℝ (childIncrementL2 μ h₂ v n) (childIncrementL2 μ h₂ v m) = 0) := by
  intro n m hnm
  rw [L2.inner_def]
  calc
    (∫ ω, inner ℝ (childIncrementL2 μ h₂ v n ω) (childIncrementL2 μ h₂ v m ω) ∂productMeasure μ) =
        ∫ ω, (pathProduct v ω ^ 2 * (ω (childEdge v n) - 1)) *
          (ω (childEdge v m) - 1) ∂productMeasure μ := by
      apply integral_congr_ae
      filter_upwards [childIncrementL2_ae μ h₂ v n, childIncrementL2_ae μ h₂ v m] with ω hn hm
      rw [hn, hm, real_inner_eq_re_inner, RCLike.inner_apply]
      simp only [conj_trivial, RCLike.re_to_real]
      ring
    _ = _ := by
      have hi := (indepFun_pathSquare_mul_child μ v hnm).integral_fun_comp_mul_comp
        (((measurable_pathProduct v).pow_const 2).mul ((measurable_pi_apply _).sub_const 1)).aemeasurable
        (measurable_pi_apply _).aemeasurable (f := id) (g := fun w : ℝ => w - 1)
        measurable_id.aestronglyMeasurable (measurable_id.sub_const 1).aestronglyMeasurable
      dsimp at hi
      rw [hi, integral_coordinate μ _ (fun w : ℝ => w - 1) (measurable_id.sub_const 1),
        integral_sub (h₂.integrable (by norm_num)) (integrable_const 1), hmean]
      simp

end ChildL2
end IndependentProducts

namespace IndependentProducts

lemma weaklyNull_child_difference (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h₂ : MemLp (fun w : ℝ => w) 2 μ) (hpos : ∀ᵐ w ∂μ, (0 : ℝ) < w)
    (hmean : ∫ w : ℝ, w ∂μ = 1) (hnot : ∀ c : ℝ, ¬ (∀ᵐ w ∂μ, w = c)) (v : Vertex) :
    WeaklyNull (fun n => pathVector μ h₂ (child v n) - pathVector μ h₂ v) := by
  have hsize : ‖l2ToL1 (productMeasure μ) (childIncrementL2 μ h₂ v 0)‖ = ∫ w : ℝ, |w - 1| ∂μ := by
    rw [l2ToL1_childIncrement]
    exact norm_child_difference μ h₂ hpos hmean v 0
  have hnorm : 0 < ‖childIncrementL2 μ h₂ v 0‖ := by
    have hh := norm_l2ToL1_le (productMeasure μ) (childIncrementL2 μ h₂ v 0)
    rw [hsize] at hh
    exact (mean_abs_deviation_pos μ h₂ hnot).trans_le hh
  have hw : WeaklyNull (childIncrementL2 μ h₂ v) :=
    weaklyNull_of_orthogonal_fixed_norm _ _ hnorm
      (childIncrementL2_norm_constant μ h₂ v) (childIncrementL2_orthogonal μ h₂ hmean v)
  intro f
  obtain ⟨g, hg, _⟩ := exists_extension_norm_eq (productSpan μ) f
  have hh := hw (g.comp (l2ToL1 (productMeasure μ)))
  have he : (fun n => f (pathVector μ h₂ (child v n) - pathVector μ h₂ v)) =
      (fun n => (g.comp (l2ToL1 (productMeasure μ))) (childIncrementL2 μ h₂ v n)) := by
    funext n
    rw [ContinuousLinearMap.comp_apply, l2ToL1_childIncrement]
    exact (hg (pathVector μ h₂ (child v n) - pathVector μ h₂ v)).symm
  rwa [he]

/-- The closed L1 product span is infinite dimensional and admits no equivalent AUC norm. -/
theorem main_general (μ : Measure ℝ) (hμ : MultiplierHypotheses μ) :
    ¬ FiniteDimensional ℝ (productSpan μ) ∧
    ∀ N : Seminorm ℝ (productSpan μ),
      IsEquivalentNorm (productSpan μ) N → ¬ IsAUC (productSpan μ) N := by
  let := hμ.probability
  have hweak := weaklyNull_child_difference μ hμ.second_moment hμ.positive hμ.mean_one hμ.nonconstant
  have hsize := norm_child_difference μ hμ.second_moment hμ.positive hμ.mean_one
  have hρ := mean_abs_deviation_pos μ hμ.second_moment hμ.nonconstant
  constructor
  · exact not_finiteDimensional_of_weaklyNull_fixed_norm (hweak []) hρ (hsize [])
  · exact bounded_tree_no_equivalent_auc (pathVector μ hμ.second_moment)
      (norm_pathVector μ hμ.second_moment hμ.positive hμ.mean_one) hρ hsize hweak

end IndependentProducts

end

end OAI

-- ---- mission target ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uX
variable (X : Type uX) [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem solution (μ : Measure ℝ) (hμ : MultiplierHypotheses μ) :
    ¬ FiniteDimensional ℝ (productSpan μ) ∧
    ∀ N : Seminorm ℝ (productSpan μ),
      IsEquivalentNorm (productSpan μ) N → ¬ IsAUC (productSpan μ) N := by
  first
    | exact OAI.IndependentProducts.main_general μ hμ
    | exact OAI.IndependentProducts.main_general X μ hμ
    | exact OAI.IndependentProducts.main_general
    | (apply OAI.IndependentProducts.main_general <;> assumption)
    | (intros; apply OAI.IndependentProducts.main_general <;> assumption)
