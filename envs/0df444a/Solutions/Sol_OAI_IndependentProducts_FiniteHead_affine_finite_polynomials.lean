-- Prove2me | solution 1 for OAI.IndependentProducts.FiniteHead.affine_finite_polynomials
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:41:06.223031+00:00
-- url     : https://prove2.me/submissions/ebdd9966-86fb-4bab-800d-0dd795fa0643

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/AffineBounds.lean:L90-L162
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.FiniteHead.affine_finite_polynomials. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns
import Definitions.Def_OAI_Analysis_ProductSpaces_MidpointModulus
import Definitions.Def_OAI_Analysis_ProductSpaces_ConditionalBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_FiniteHeads
import Definitions.Def_OAI_Analysis_ProductSpaces_Resampling
import Definitions.Def_OAI_Analysis_ProductSpaces_ClosedTails
import Definitions.Def_OAI_Analysis_ProductSpaces_TailCoefficients
import Theorems.Thm_OAI_IndependentProducts_FiniteHead_boundary_eq_of_prefix
import Theorems.Thm_OAI_IndependentProducts_FiniteHead_integral_tailCoefficient
import Theorems.Thm_OAI_IndependentProducts_FiniteHead_stitched_path
import Theorems.Thm_OAI_IndependentProducts_integrated_first_exit_affine
import Theorems.Thm_OAI_IndependentProducts_measurePreserving_sampleSelector
import Theorems.Thm_OAI_IndependentProducts_mem_pathEdges_iff
import Theorems.Thm_OAI_IndependentProducts_midpointGain_eq_integral_excess
import Theorems.Thm_OAI_IndependentProducts_representative_sum

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

lemma integrable_finset_coordinates_prod (s : Finset Edge) (f : Edge → ℝ → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i) μ) :
    Integrable (fun ω : Sample => ∏ i ∈ s, f i (ω i)) (productMeasure μ) := by
  have hi := integrable_coordinates_prod μ (fun i : s => i.val) Subtype.val_injective
    (fun i : s => f i) (fun i => hf i i.property)
  have he : (fun ω : Sample => ∏ i : s, f i (ω i)) = fun ω => ∏ i ∈ s, f i (ω i) :=
    funext (fun ω => s.prod_coe_sort (fun i => f i (ω i)))
  rwa [he] at hi

end CoordinateProducts
end IndependentProducts

namespace IndependentProducts

section ChildMoments
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

end ChildMoments
end IndependentProducts

end

end OAI

-- ---- from OAI.Analysis.ProductSpaces.RandomSigns ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΩ uι

namespace IndependentProducts

lemma euclidSize_nonneg {ι : Type uι} [Fintype ι] (a : ι → ℝ) : 0 ≤ euclidSize a := Real.sqrt_nonneg _

lemma euclidSize_sq {ι : Type uι} [Fintype ι] (a : ι → ℝ) : euclidSize a ^ 2 = ∑ i, a i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma euclidSize_le_sum_abs {ι : Type uι} [Fintype ι] (a : ι → ℝ) :
    euclidSize a ≤ ∑ i, |a i| := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun i _ => abs_nonneg (a i))
  simp only [sq_abs] at h
  have hsum : 0 ≤ ∑ i, |a i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  nlinarith [euclidSize_sq a, euclidSize_nonneg a]

lemma integrable_euclidSize {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} (X : ι → Ω → ℝ) (hX : ∀ i, Integrable (X i) P) :
    Integrable (fun ω => euclidSize (fun i => X i ω)) P := by
  apply Integrable.mono' (integrable_finsetSum _ (fun i _ => (hX i).abs))
  · unfold euclidSize
    fun_prop
  · exact ae_of_all _ (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (euclidSize_nonneg _)]
      exact euclidSize_le_sum_abs _)

section SignVector
variable {ι : Type uι} [Fintype ι]

end SignVector
end IndependentProducts

namespace IndependentProducts
section Symmetrization
variable {ι : Type uι} [Fintype ι]

end Symmetrization
end IndependentProducts

end

end OAI

-- ---- from OAI.Analysis.ProductSpaces.FiniteHeads ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uκ

namespace IndependentProducts
namespace FiniteHead
variable (T : FiniteHead)

lemma boundary_unique {v : Vertex} {e f : T.Boundary}
    (he : e.val.val <+: v) (hf : f.val.val <+: v) : e = f := by
  rcases List.prefix_or_prefix_of_prefix he hf with h | h
  · exact T.boundary_eq_of_prefix h
  · exact (T.boundary_eq_of_prefix h).symm

lemma exit_prefix (v : Vertex) (hv : v ∉ T.vertices) : (T.exit v hv).val.val <+: v :=
  Classical.choose_spec (T.exists_boundary_prefix v hv)

lemma exit_eq (v : Vertex) (hv : v ∉ T.vertices) (e : T.Boundary)
    (he : e.val.val <+: v) : T.exit v hv = e := T.boundary_unique (T.exit_prefix v hv) he

lemma ancestor_mem (v : Vertex) : T.ancestor v ∈ T.vertices := by
  unfold ancestor
  split_ifs with h
  · exact h
  · exact (T.exit v h).property.2

lemma ancestor_of_not_mem {v : Vertex} (hv : v ∉ T.vertices) :
    T.ancestor v = (T.exit v hv).val.val.dropLast := by simp [ancestor, hv]

lemma no_boundary_prefix_head {v : Vertex} (hv : v ∈ T.vertices) (e : T.Boundary) :
    ¬ e.val.val <+: v := fun h => e.property.1 (T.prefix_mem h hv)

end FiniteHead
end IndependentProducts

namespace IndependentProducts

section Selector
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

end Selector
end IndependentProducts

end

end OAI

-- ---- from OAI.Analysis.ProductSpaces.Resampling ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι

namespace IndependentProducts

section Resampling
variable {ι : Type uι} [Fintype ι]

lemma measurePreserving_expandSamples (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MeasurePreserving (expandSamples (ι := ι))
      (((Measure.pi (fun _ : ι => productMeasure μ)).prod (productMeasure μ)).prod (productMeasure μ))
      (Measure.pi (fun _ : Option (Option ι) => productMeasure μ)) := by
  have h1 : MeasurePreserving (MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => Sample)).symm
      ((Measure.pi (fun _ : ι => productMeasure μ)).prod (productMeasure μ))
      (Measure.pi (fun _ : Option ι => productMeasure μ)) :=
    ⟨by fun_prop, Measure.pi_map_piOptionEquivProd (fun _ : Option ι => productMeasure μ)⟩
  have h2 : MeasurePreserving (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Option ι) => Sample)).symm
      ((Measure.pi (fun _ : Option ι => productMeasure μ)).prod (productMeasure μ))
      (Measure.pi (fun _ : Option (Option ι) => productMeasure μ)) :=
    ⟨by fun_prop, Measure.pi_map_piOptionEquivProd (fun _ : Option (Option ι) => productMeasure μ)⟩
  convert h2.comp (h1.prod (MeasurePreserving.id (productMeasure μ))) using 1
  ext z k e
  cases k with
  | none => rfl
  | some k => cases k <;> rfl

namespace FiniteHead
variable (T : FiniteHead) (e : ι → T.Boundary) (he : Function.Injective e)

lemma sampleSelector_head {d : Edge} (hd : d.val ∈ T.vertices) :
    T.sampleSelector e d = none := by
  classical
  have hn : ¬ ∃ i, (e i).val.val <+: d.val := by
    rintro ⟨i, hi⟩
    exact T.no_boundary_prefix_head hd (e i) hi
  simp [sampleSelector, hn]

lemma measurePreserving_stitched (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MeasurePreserving (T.stitched e)
      (((Measure.pi (fun _ : ι => productMeasure μ)).prod (productMeasure μ)).prod (productMeasure μ))
      (productMeasure μ) :=
  (measurePreserving_sampleSelector μ (T.sampleSelector e)).comp (measurePreserving_expandSamples μ)

lemma stitched_head (z : ((ι → Sample) × Sample) × Sample) (v : Vertex) (hv : v ∈ T.vertices) :
    pathProduct v (T.stitched e z) = pathProduct v z.2 := by
  simp only [pathProduct_eq_prod_pathEdges]
  apply Finset.prod_congr rfl
  intro d hd
  have hdt : d.val ∈ T.vertices := T.prefix_mem ((mem_pathEdges_iff v d).mp hd) hv
  simp [stitched, T.sampleSelector_head e hdt, expandSamples]

end FiniteHead

namespace FiniteHead
variable (T : FiniteHead) (e : ι → T.Boundary) (he : Function.Injective e)

end FiniteHead
end Resampling
end IndependentProducts

end

end OAI

-- ---- from OAI.Analysis.ProductSpaces.TailCoefficients ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι uκ

namespace IndependentProducts
section FiniteRepresentatives
variable (μ : Measure ℝ) [hμprob : IsProbabilityMeasure μ]
  (h₂ : MemLp (fun w : ℝ => w) 2 μ)

lemma pathVector_ae (v : Vertex) :
    ((pathVector μ h₂ v).val : Sample → ℝ) =ᵐ[productMeasure μ] pathProduct v := pathL1_ae μ h₂ v

omit hμprob in
lemma representative_sub [IsProbabilityMeasure μ] (x y : productSpan μ) (f g : Sample → ℝ)
    (hf : x.val =ᵐ[productMeasure μ] f) (hg : y.val =ᵐ[productMeasure μ] g) :
    ((x - y).val : Sample → ℝ) =ᵐ[productMeasure μ] fun ω => f ω - g ω := by
  change (↑(x.val - y.val) : Sample → ℝ) =ᵐ[productMeasure μ] _
  filter_upwards [Lp.coeFn_sub x.val y.val, hf, hg] with ω he hx hy
  simpa only [Pi.sub_apply, hx, hy] using he

omit hμprob in
lemma norm_eq_integral_abs_rep [IsProbabilityMeasure μ] (x : productSpan μ) (f : Sample → ℝ)
    (hf : x.val =ᵐ[productMeasure μ] f) : ‖x‖ = ∫ ω, |f ω| ∂productMeasure μ := by
  change ‖x.val‖ = _
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [hf] with ω hω
  simp only [hω, Real.norm_eq_abs]

lemma integrable_rep (x : productSpan μ) (f : Sample → ℝ)
    (hf : x.val =ᵐ[productMeasure μ] f) : Integrable f (productMeasure μ) :=
  ((Lp.memLp x.val).integrable le_rfl).congr hf

namespace FiniteHead
variable (T : FiniteHead)

lemma relativeVector_ae (v : Vertex) :
    ((T.relativeVector μ h₂ v).val : Sample → ℝ) =ᵐ[productMeasure μ]
      fun ω => pathProduct v ω - pathProduct (T.ancestor v) ω :=
  representative_sub μ _ _ _ _ (pathVector_ae μ h₂ v) (pathVector_ae μ h₂ (T.ancestor v))

end FiniteHead
end FiniteRepresentatives

lemma measurable_residualProduct (v : Vertex) (e : Edge) : Measurable (residualProduct v e) := by
  unfold residualProduct
  fun_prop

lemma integrable_residualProduct (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hw : Integrable (fun w : ℝ => w) μ) (v : Vertex) (e : Edge) :
    Integrable (residualProduct v e) (productMeasure μ) :=
  integrable_finset_coordinates_prod μ _ _ (fun _ _ => hw)

namespace FiniteHead
section FiniteTailData
variable {ι : Type uι} {κ : Type uκ} [hιfinite : Fintype ι] [Fintype κ] [DecidableEq ι]
variable (T : FiniteHead) (e : ι → T.Boundary) (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ)

lemma measurable_tailCoefficient {ι : Type uι} {κ : Type uκ}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (T : FiniteHead) (e : ι → T.Boundary) (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ) (i : ι) :
    Measurable (fun z : Sample × Sample => T.tailCoefficient e v j a z.1 i z.2) := by
  classical
  unfold tailCoefficient
  apply Finset.measurable_sum
  intro k hk
  split_ifs
  · exact ((measurable_const.mul ((measurable_pathProduct _).comp measurable_fst)).mul
      ((measurable_residualProduct _ _).comp measurable_snd))
  · fun_prop

lemma integrable_tailCoefficient {ι : Type uι} {κ : Type uκ}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (T : FiniteHead) (e : ι → T.Boundary) (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hw : Integrable (fun w : ℝ => w) μ) (old : Sample) (i : ι) :
    Integrable (T.tailCoefficient e v j a old i) (productMeasure μ) := by
  classical
  apply integrable_finsetSum
  intro k hk
  split_ifs
  · exact (integrable_residualProduct μ hw _ _).const_mul _
  · exact integrable_zero _ _ _

lemma sum_tailCoefficient (z : ((ι → Sample) × Sample) × Sample)
    (he : Function.Injective e) (hv : ∀ k, (e (j k)).val.val <+: v k) :
    ∑ k, a k * pathProduct (v k) (T.stitched e z) =
      ∑ i, T.tailCoefficient e v j a z.2 i (z.1.1 i) * z.1.2 (e i).val := by
  classical
  simp only [tailCoefficient, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [T.stitched_path e he z (v k) (j k) (hv k)]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, residualProduct]
  ring

lemma sum_tailCoefficient_mean (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hw : Integrable (fun w : ℝ => w) μ) (hm : ∫ w : ℝ, w ∂μ = 1)
    (old : Sample) :
    ∑ i, ∫ desc, T.tailCoefficient e v j a old i desc ∂productMeasure μ =
      ∑ k, a k * pathProduct (e (j k)).val.val.dropLast old := by
  classical
  simp_rw [T.integral_tailCoefficient e v j a μ hw hm old]
  rw [Finset.sum_comm]
  congr 1
  ext k
  simp

end FiniteTailData
end FiniteHead
end IndependentProducts

end

end OAI

-- ---- from OAI.Analysis.ProductSpaces.CoefficientLaw ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι uκ

namespace IndependentProducts
namespace FiniteHead
lemma ancestor_of_boundary_prefix (T : FiniteHead) (v : Vertex) (e : T.Boundary)
    (he : e.val.val <+: v) : T.ancestor v = e.val.val.dropLast := by
  have hv : v ∉ T.vertices := fun hv => T.no_boundary_prefix_head hv e he
  rw [T.ancestor_of_not_mem hv, T.exit_eq v hv e he]

section CoefficientJoint
variable {ι : Type uι} {κ : Type uκ} [hιfinite : Fintype ι] [Fintype κ]
  [hιdecidable : DecidableEq ι]
variable (T : FiniteHead) (e : ι → T.Boundary) (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ)
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (h₂ : MemLp (fun w : ℝ => w) 2 μ)

lemma integrable_tailCoefficient_joint {ι : Type uι} {κ : Type uκ}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (T : FiniteHead) (e : ι → T.Boundary) (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (h₂ : MemLp (fun w : ℝ => w) 2 μ) (i : ι) :
    Integrable (fun z : Sample × Sample => T.tailCoefficient e v j a z.1 i z.2)
      ((productMeasure μ).prod (productMeasure μ)) := by
  classical
  unfold tailCoefficient
  apply integrable_finsetSum
  intro k hk
  split_ifs
  · exact (((pathProduct_memLp μ h₂ _).integrable (by norm_num)).const_mul _).mul_prod
      (integrable_residualProduct μ (h₂.integrable (by norm_num)) _ _)
  · exact integrable_zero _ _ _

include h₂ in
lemma integrable_tailCoefficient_all (i : ι) :
    Integrable (fun z : (ι → Sample) × Sample => T.tailCoefficient e v j a z.2 i (z.1 i))
      ((Measure.pi (fun _ : ι => productMeasure μ)).prod (productMeasure μ)) := by
  have hmp : MeasurePreserving (fun z : (ι → Sample) × Sample => (z.2, z.1 i))
      ((Measure.pi (fun _ : ι => productMeasure μ)).prod (productMeasure μ))
      ((productMeasure μ).prod (productMeasure μ)) := by
    exact (Measure.measurePreserving_swap (μ := productMeasure μ) (ν := productMeasure μ)).comp
      ((measurePreserving_eval (fun _ : ι => productMeasure μ) i).prod (MeasurePreserving.id _))
  exact hmp.integrable_comp (T.measurable_tailCoefficient e v j a i).aestronglyMeasurable |>.mpr
    (T.integrable_tailCoefficient_joint e v j a μ h₂ i)

include h₂ in
lemma stitched_tail_polynomial (z : ((ι → Sample) × Sample) × Sample)
    (he : Function.Injective e) (hv : ∀ k, (e (j k)).val.val <+: v k)
    (hmean : ∫ w : ℝ, w ∂μ = 1) :
    (∑ k, a k * (pathProduct (v k) (T.stitched e z) -
      pathProduct (T.ancestor (v k)) (T.stitched e z))) =
      ∑ i, (T.tailCoefficient e v j a z.2 i (z.1.1 i) * z.1.2 (e i).val -
        ∫ desc, T.tailCoefficient e v j a z.2 i desc ∂productMeasure μ) := by
  classical
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [T.sum_tailCoefficient e v j a z he hv,
    T.sum_tailCoefficient_mean e v j a μ (h₂.integrable (by norm_num)) hmean z.2]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [T.stitched_head e z _ (T.ancestor_mem _), T.ancestor_of_boundary_prefix (v k) (e (j k)) (hv k)]

lemma stitched_head_polynomial {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (T : FiniteHead) (e : ι → T.Boundary) (a : T.vertices → ℝ)
    (z : ((ι → Sample) × Sample) × Sample) :
    (∑ v : T.vertices, a v * pathProduct v (T.stitched e z)) =
      ∑ v : T.vertices, a v * pathProduct v z.2 := by
  apply Finset.sum_congr rfl
  intro v hv
  rw [T.stitched_head e z v v.property]

end CoefficientJoint
end FiniteHead
end IndependentProducts

end

end OAI

-- ---- from OAI.Analysis.ProductSpaces.AffineBounds ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uO uR uS uΛ uΩ uι

namespace IndependentProducts
section MeasureDiagram
variable {S : Type uS} {R : Type uR} {O : Type uO}
  [MeasurableSpace S] [MeasurableSpace R] [MeasurableSpace O]
variable {Ps : Measure S} {Pr : Measure R} {Po : Measure O} {q : S → R} {s : S → O}

lemma integral_measure_diagram (hq : MeasurePreserving q Ps Pr) (hs : MeasurePreserving s Ps Po)
    (f : R → ℝ) (g : O → ℝ) (hf : Measurable f) (hg : Measurable g)
    (he : ∀ z, f (q z) = g (s z)) : ∫ z, f z ∂Pr = ∫ ω, g ω ∂Po := by
  rw [← hq.hasLaw.integral_comp hf.aestronglyMeasurable,
    ← hs.hasLaw.integral_comp hg.aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ he)

lemma integrable_measure_diagram (hq : MeasurePreserving q Ps Pr) (hs : MeasurePreserving s Ps Po)
    (f : R → ℝ) (g : O → ℝ) (hf : Measurable f) (hg : Measurable g)
    (he : ∀ z, f (q z) = g (s z)) (hi : Integrable g Po) : Integrable f Pr := by
  apply (hq.integrable_comp hf.aestronglyMeasurable).mp
  apply Integrable.congr ((hs.integrable_comp hg.aestronglyMeasurable).mpr hi)
  exact Filter.EventuallyEq.symm (ae_of_all Ps he)

end MeasureDiagram

lemma measurable_joint_firstExitSum {Λ : Type uΛ} {Ω : Type uΩ} {ι : Type uι}
    [MeasurableSpace Λ] [MeasurableSpace Ω]
    [Fintype ι] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (B : Λ → ι → Ω → ℝ)
    (hB : ∀ i, Measurable (fun z : Λ × Ω => B z.1 i z.2))
    (hm : ∀ i, Measurable (fun l => ∫ b, B l i b ∂ν)) :
    Measurable (fun z : ((ι → Ω) × (ι → ℝ)) × Λ => firstExitSum ν (B z.2) z.1) := by
  unfold firstExitSum
  apply Finset.measurable_sum
  intro i hi
  exact (((hB i).comp
    (measurable_snd.prodMk ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)))).mul
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst))).sub
        ((hm i).comp measurable_snd)

namespace FiniteHead
section FiniteAffine
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (h₂ : MemLp (fun w : ℝ => w) 2 μ)
variable (hmean : ∫ w : ℝ, w ∂μ = 1)
variable (T : FiniteHead) (e : ι → T.Boundary) (he : Function.Injective e)
variable (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ) (hv : ∀ k, (e (j k)).val.val <+: v k)

include h₂ hmean in
lemma measurable_tailCoefficient_mean (i : ι) :
    Measurable (fun old => ∫ desc, T.tailCoefficient e v j a old i desc ∂productMeasure μ) := by
  classical
  have hm : Measurable (fun old => ∑ k, if j k = i then
      a k * pathProduct (e i).val.val.dropLast old else 0) := by
    apply Finset.measurable_sum
    intro k hk
    by_cases h : j k = i
    · simp only [h, ite_true]
      exact (measurable_pathProduct _).const_mul (a k)
    · simp only [h, ite_false]
      exact measurable_const
  have he : (fun old => ∫ desc, T.tailCoefficient e v j a old i desc ∂productMeasure μ) =
      (fun old => ∑ k, if j k = i then a k * pathProduct (e i).val.val.dropLast old else 0) :=
    funext (fun old => T.integral_tailCoefficient e v j a μ (h₂.integrable (by norm_num)) hmean old i)
  rw [he]
  exact hm

include h₂ hmean in
lemma measurable_resampled_tail :
    Measurable (fun z : ((ι → Sample) × (ι → ℝ)) × Sample =>
      firstExitSum (productMeasure μ) (T.tailCoefficient e v j a z.2) z.1) := by
  classical
  exact measurable_joint_firstExitSum (productMeasure μ) (T.tailCoefficient e v j a)
    (T.measurable_tailCoefficient e v j a)
    (measurable_tailCoefficient_mean μ h₂ hmean T e v j a)

lemma measurable_tailCoefficient_section (old : Sample) (i : ι) :
    Measurable (T.tailCoefficient e v j a old i) :=
  Measurable.of_uncurry_left (f := fun old desc => T.tailCoefficient e v j a old i desc)
    (T.measurable_tailCoefficient e v j a i)

include hmean he hv in
lemma affine_finite_polynomials (c : T.vertices → ℝ) (t A D : ℝ) (ht : 0 ≤ t) (hA : 0 ≤ A)
    (hC : 0 < 2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))
    (hscalar : ∀ aa : ι → ℝ, ∀ b r : ℝ, 0 ≤ r →
      A * euclidSize aa - D * r ≤
        ∫ w : ι → ℝ, excess t r (b + ∑ i, aa i * w i) ∂Measure.pi (fun _ : ι => μ)) :
    (A / (2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))) *
      ‖∑ k, a k • T.relativeVector μ h₂ (v k)‖ -
      D * ‖∑ v : T.vertices, c v • pathVector μ h₂ v‖ ≤
      midpointGain t (∑ v : T.vertices, c v • pathVector μ h₂ v)
        (∑ k, a k • T.relativeVector μ h₂ (v k)) := by
  classical
  let P := productMeasure μ
  let Pb := Measure.pi (fun _ : ι => P)
  let Pw := Measure.pi (fun _ : ι => μ)
  let Ps := (Pb.prod P).prod P
  let Pr := (Pb.prod Pw).prod P
  let U : Sample → ℝ := fun old => ∑ v : T.vertices, c v * pathProduct v old
  let V : Sample → ℝ := fun ω => ∑ k, a k * (pathProduct (v k) ω - pathProduct (T.ancestor (v k)) ω)
  let B := T.tailCoefficient e v j a
  let Y : ((ι → Sample) × (ι → ℝ)) × Sample → ℝ := fun z => firstExitSum P (B z.2) z.1
  let q : ((ι → Sample) × Sample) × Sample → ((ι → Sample) × (ι → ℝ)) × Sample :=
    fun z => ((z.1.1, fun i => z.1.2 (e i).val), z.2)
  have hq : MeasurePreserving q Ps Pr :=
    ((MeasurePreserving.id Pb).prod (measurePreserving_coordinates μ (fun i => (e i).val)
      (Subtype.val_injective.comp he))).prod (MeasurePreserving.id P)
  have hst := T.measurePreserving_stitched e μ
  have hUm : Measurable U := Finset.measurable_sum _
    (fun v _ => (measurable_pathProduct v).const_mul (c v))
  have hVm : Measurable V := Finset.measurable_sum _
    (fun k _ => ((measurable_pathProduct (v k)).sub (measurable_pathProduct (T.ancestor (v k)))).const_mul (a k))
  have hYm : Measurable Y := T.measurable_resampled_tail μ h₂ hmean e v j a
  have heU : ∀ z : ((ι → Sample) × Sample) × Sample, U (q z).2 = U (T.stitched e z) := by
    intro z
    exact (T.stitched_head_polynomial e c z).symm
  have heY : ∀ z : ((ι → Sample) × Sample) × Sample, Y (q z) = V (T.stitched e z) := by
    intro z
    exact (T.stitched_tail_polynomial e v j a μ h₂ z he hv hmean).symm
  let x : productSpan μ := ∑ v : T.vertices, c v • pathVector μ h₂ v
  let y : productSpan μ := ∑ k, a k • T.relativeVector μ h₂ (v k)
  have hx : (x.val : Sample → ℝ) =ᵐ[P] U :=
    representative_sum μ (fun v : T.vertices => pathVector μ h₂ v)
      (fun v : T.vertices => pathProduct v) (fun v => pathVector_ae μ h₂ v) c
  have hy : (y.val : Sample → ℝ) =ᵐ[P] V :=
    representative_sum μ _ _ (fun k => T.relativeVector_ae μ h₂ (v k)) a
  have hUi : Integrable U P := integrable_rep μ x U hx
  have hVi : Integrable V P := integrable_rep μ y V hy
  have hYi : Integrable Y Pr := integrable_measure_diagram hq hst Y V hYm hVm heY hVi
  have hSi : Integrable (fun z : (ι → Sample) × Sample => euclidSize (fun i => B z.2 i (z.1 i)))
      (Pb.prod P) := integrable_euclidSize _ (T.integrable_tailCoefficient_all e v j a μ h₂)
  have hBi : ∀ old i, Integrable (B old i) P :=
    T.integrable_tailCoefficient e v j a μ (h₂.integrable (by norm_num))
  have hBm : ∀ old i, Measurable (B old i) := by
    intro old i
    exact measurable_tailCoefficient_section T e v j a old i
  have ha := integrated_first_exit_affine μ P P h₂ hmean B hBi hBm U hUi hSi hYi
    t A D hA hC hscalar
  have hnY : (∫ z, |Y z| ∂Pr) = ‖y‖ := by
    rw [integral_measure_diagram hq hst (fun z => |Y z|) (fun ω => |V ω|)
      hYm.abs hVm.abs (fun z => congrArg abs (heY z))]
    exact (norm_eq_integral_abs_rep μ y V hy).symm
  have hnU : (∫ old, |U old| ∂P) = ‖x‖ := (norm_eq_integral_abs_rep μ x U hx).symm
  have hg : (∫ z, excess t |U z.2| (Y z) ∂Pr) = midpointGain t x y := by
    rw [integral_measure_diagram hq hst (fun z => excess t |U z.2| (Y z))
      (fun ω => excess t |U ω| (V ω))
      (by unfold excess; exact (((hYm.abs.const_mul t).sub ((hUm.comp measurable_snd).abs)).max measurable_const))
      (by unfold excess; exact ((hVm.abs.const_mul t).sub hUm.abs).max measurable_const)
      (fun z => by rw [heU z, heY z])]
    exact (midpointGain_eq_integral_excess P x.val y.val U V hx hy t ht).symm
  change A / (2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ)) * (∫ z, |Y z| ∂Pr) -
    D * (∫ old, |U old| ∂P) ≤ ∫ z, excess t |U z.2| (Y z) ∂Pr at ha
  rw [hnY, hnU, hg] at ha
  exact ha

end FiniteAffine
end FiniteHead
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts OAI.IndependentProducts.FiniteHead
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uO uR uS uΛ uΩ uι
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (h₂ : MemLp (fun w : ℝ => w) 2 μ)
variable (hmean : ∫ w : ℝ, w ∂μ = 1)
variable (T : FiniteHead) (e : ι → T.Boundary) (he : Function.Injective e)
variable (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ) (hv : ∀ k, (e (j k)).val.val <+: v k)

include hmean he hv in
theorem solution (c : T.vertices → ℝ) (t A D : ℝ) (ht : 0 ≤ t) (hA : 0 ≤ A)
    (hC : 0 < 2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))
    (hscalar : ∀ aa : ι → ℝ, ∀ b r : ℝ, 0 ≤ r →
      A * euclidSize aa - D * r ≤
        ∫ w : ι → ℝ, excess t r (b + ∑ i, aa i * w i) ∂Measure.pi (fun _ : ι => μ)) :
    (A / (2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))) *
      ‖∑ k, a k • T.relativeVector μ h₂ (v k)‖ -
      D * ‖∑ v : T.vertices, c v • pathVector μ h₂ v‖ ≤
      midpointGain t (∑ v : T.vertices, c v • pathVector μ h₂ v)
        (∑ k, a k • T.relativeVector μ h₂ (v k)) := by
  first
    | exact OAI.IndependentProducts.FiniteHead.affine_finite_polynomials c t A D ht hA hC hscalar
    | exact OAI.IndependentProducts.FiniteHead.affine_finite_polynomials μ h₂ hmean T e he v j a hv c t A D ht hA hC hscalar
    | exact OAI.IndependentProducts.FiniteHead.affine_finite_polynomials
    | (apply OAI.IndependentProducts.FiniteHead.affine_finite_polynomials <;> assumption)
    | (intros; apply OAI.IndependentProducts.FiniteHead.affine_finite_polynomials <;> assumption)
