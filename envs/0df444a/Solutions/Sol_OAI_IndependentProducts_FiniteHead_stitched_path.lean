-- Prove2me | solution 1 for OAI.IndependentProducts.FiniteHead.stitched_path
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:33:28.00269+00:00
-- url     : https://prove2.me/submissions/b35ad7ae-5a66-49b3-85b9-5ec0606d7e64

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/Resampling.lean:L105-L126
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.FiniteHead.stitched_path. The node keeps its source
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
import Theorems.Thm_OAI_IndependentProducts_FiniteHead_boundary_eq_of_prefix
import Theorems.Thm_OAI_IndependentProducts_mem_pathEdges_iff
import Theorems.Thm_OAI_IndependentProducts_pathEdges_parent

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

end CoordinateProducts
end IndependentProducts

namespace IndependentProducts

section ChildMoments
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

end ChildMoments
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

lemma no_boundary_prefix_head {v : Vertex} (hv : v ∈ T.vertices) (e : T.Boundary) :
    ¬ e.val.val <+: v := fun h => e.property.1 (T.prefix_mem h hv)

end FiniteHead
end IndependentProducts

namespace IndependentProducts

lemma pathEdges_mono {u v : Vertex} (h : u <+: v) : pathEdges u ⊆ pathEdges v := by
  intro e he
  exact (mem_pathEdges_iff v e).mpr (((mem_pathEdges_iff u e).mp he).trans h)

lemma self_mem_pathEdges (e : Edge) : e ∈ pathEdges e.val :=
  (mem_pathEdges_iff _ _).mpr List.prefix_rfl

lemma self_not_mem_pathEdges_parent (e : Edge) : e ∉ pathEdges e.val.dropLast := by
  intro h
  have hh := ((mem_pathEdges_iff _ _).mp h).length_le
  have hp : 0 < e.val.length := List.length_pos_iff.mpr e.property
  simp only [List.length_dropLast] at hh
  omega

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

namespace FiniteHead
variable (T : FiniteHead) (e : ι → T.Boundary) (he : Function.Injective e)

lemma sampleSelector_head {d : Edge} (hd : d.val ∈ T.vertices) :
    T.sampleSelector e d = none := by
  classical
  have hn : ¬ ∃ i, (e i).val.val <+: d.val := by
    rintro ⟨i, hi⟩
    exact T.no_boundary_prefix_head hd (e i) hi
  simp [sampleSelector, hn]

include he in
lemma sampleSelector_exit (i : ι) : T.sampleSelector e (e i).val = some none := by
  classical
  have hh : ∃ j, (e j).val.val <+: (e i).val.val := ⟨i, List.prefix_rfl⟩
  have hi : Classical.choose hh = i := he (T.boundary_eq_of_prefix (Classical.choose_spec hh))
  simp [sampleSelector, hh, hi]

include he in
lemma sampleSelector_desc (i : ι) (d : Edge) (hd : (e i).val.val <+: d.val)
    (hne : d ≠ (e i).val) : T.sampleSelector e d = some (some i) := by
  classical
  have hh : ∃ j, (e j).val.val <+: d.val := ⟨i, hd⟩
  have hi : Classical.choose hh = i := he (T.boundary_unique (Classical.choose_spec hh) hd)
  simp [sampleSelector, hh, hi, hne]

lemma stitched_head (z : ((ι → Sample) × Sample) × Sample) (v : Vertex) (hv : v ∈ T.vertices) :
    pathProduct v (T.stitched e z) = pathProduct v z.2 := by
  simp only [pathProduct_eq_prod_pathEdges]
  apply Finset.prod_congr rfl
  intro d hd
  have hdt : d.val ∈ T.vertices := T.prefix_mem ((mem_pathEdges_iff v d).mp hd) hv
  simp [stitched, T.sampleSelector_head e hdt, expandSamples]

end FiniteHead

lemma pathProduct_split (v : Vertex) (e : Edge) (he : e.val <+: v) (ω : Sample) :
    pathProduct v ω = pathProduct e.val.dropLast ω * ω e *
      ∏ d ∈ pathEdges v \ pathEdges e.val, ω d := by
  classical
  have h := Finset.prod_sdiff (f := ω) (pathEdges_mono he)
  rw [pathEdges_parent, Finset.prod_insert (self_not_mem_pathEdges_parent e)] at h
  simp only [pathProduct_eq_prod_pathEdges]
  rw [← h, pathEdges_parent]
  ring

namespace FiniteHead
variable (T : FiniteHead) (e : ι → T.Boundary) (he : Function.Injective e)

include he in
lemma stitched_path (z : ((ι → Sample) × Sample) × Sample) (v : Vertex) (i : ι)
    (hi : (e i).val.val <+: v) :
    pathProduct v (T.stitched e z) = pathProduct (e i).val.val.dropLast z.2 * z.1.2 (e i).val *
      ∏ d ∈ pathEdges v \ pathEdges (e i).val.val, z.1.1 i d := by
  classical
  rw [pathProduct_split v (e i).val hi, T.stitched_head e z _ (e i).property.2]
  have hw : T.stitched e z (e i).val = z.1.2 (e i).val := by
    simp [stitched, T.sampleSelector_exit e he i, expandSamples]
  rw [hw]
  congr 1
  apply Finset.prod_congr rfl
  intro d hd
  obtain ⟨hdv, hde⟩ := Finset.mem_sdiff.mp hd
  have hp : (e i).val.val <+: d.val := by
    rcases List.prefix_or_prefix_of_prefix hi ((mem_pathEdges_iff v d).mp hdv) with h | h
    · exact h
    · exact (hde ((mem_pathEdges_iff _ _).mpr h)).elim
  have hne : d ≠ (e i).val := by
    rintro rfl
    exact hde (self_mem_pathEdges _)
  simp [stitched, T.sampleSelector_desc e he i d hp hne, expandSamples]

end FiniteHead
end Resampling
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts OAI.IndependentProducts.FiniteHead
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uι
variable {ι : Type uι} [Fintype ι]
variable (T : FiniteHead) (e : ι → T.Boundary) (he : Function.Injective e)

include he in
theorem solution (z : ((ι → Sample) × Sample) × Sample) (v : Vertex) (i : ι)
    (hi : (e i).val.val <+: v) :
    pathProduct v (T.stitched e z) = pathProduct (e i).val.val.dropLast z.2 * z.1.2 (e i).val *
      ∏ d ∈ pathEdges v \ pathEdges (e i).val.val, z.1.1 i d := by
  first
    | exact OAI.IndependentProducts.FiniteHead.stitched_path z v i hi
    | exact OAI.IndependentProducts.FiniteHead.stitched_path T e he z v i hi
    | exact OAI.IndependentProducts.FiniteHead.stitched_path
    | (apply OAI.IndependentProducts.FiniteHead.stitched_path <;> assumption)
    | (intros; apply OAI.IndependentProducts.FiniteHead.stitched_path <;> assumption)
