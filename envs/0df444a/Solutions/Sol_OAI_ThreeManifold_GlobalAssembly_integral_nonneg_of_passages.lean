-- Prove2me | solution 1 for OAI.ThreeManifold.GlobalAssembly.integral_nonneg_of_passages
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:07:58.793301+00:00
-- url     : https://prove2.me/submissions/573c2abd-5bc4-496a-8786-93e49fc25da3

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Index.lean:L1310-L1325
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.GlobalAssembly.integral_nonneg_of_passages. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning
import Definitions.Def_OAI_Geometry_ConjugatePoints_Index
import Theorems.Thm_OAI_ThreeManifold_GlobalAssembly_passages_disjoint

-- ---- from OAI.Geometry.ConjugatePoints.Index ----
namespace OAI

noncomputable section

/-!
# Index forms, cutoff fields, and assembly of local estimates.
-/

section

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
namespace ThreeManifold.IndexCutoff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

end ThreeManifold.IndexCutoff

open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace ThreeManifold.IndexForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

end ThreeManifold.IndexForm

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace
namespace ThreeManifold.IndexForm

section
open IndexCutoff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

end

section
open IndexCutoff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

end

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

end

open IndexCutoff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

end ThreeManifold.IndexForm
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter MeasureTheory Real
open scoped Topology ContDiff
namespace ThreeManifold.IndexCutoff

end ThreeManifold.IndexCutoff
end

section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace ThreeManifold.IndexCutoff

end ThreeManifold.IndexCutoff
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
open IndexCutoff

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
open IndexCutoff

end ThreeManifold.RiemannianCoordinates
end

open Set MeasureTheory Topology Function

namespace ThreeManifold.GlobalAssembly

lemma passages_open {U : Set ℝ} (hU : IsOpen U) (J : Passages U) : IsOpen J.val := by
  obtain ⟨x, _, hxJ⟩ := J.property
  rw [hxJ]
  exact hU.connectedComponentIn

lemma passages_nonempty {U : Set ℝ} (J : Passages U) : J.val.Nonempty := by
  obtain ⟨x, hx, hxJ⟩ := J.property
  rw [hxJ]
  exact connectedComponentIn_nonempty_iff.mpr hx

lemma passages_countable {U : Set ℝ} (hU : IsOpen U) : Countable (Passages U) :=
  (passages_disjoint U).countable_of_isOpen_disjoint (passages_open hU) passages_nonempty

lemma passages_cover (U : Set ℝ) : (⋃ J : Passages U, J.val) = U := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨J, hxJ⟩ := mem_iUnion.mp hx
    obtain ⟨j, _, hj⟩ := J.property
    exact connectedComponentIn_subset U j (hj ▸ hxJ)
  · intro x hx
    exact mem_iUnion.mpr ⟨⟨connectedComponentIn U x, x, hx, rfl⟩, mem_connectedComponentIn hx⟩

theorem density_assembly {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ} (hf : Integrable f) :
    HasSum (fun J : Passages U => ∫ s in J.val, f s) (∫ s in U, f s) ∧
      (∫ s in U, f s) + (∫ s in Uᶜ, f s) = ∫ s, f s := by
  let := passages_countable hU
  constructor
  · convert! hasSum_integral_iUnion (fun J : Passages U => (passages_open hU J).measurableSet)
      (passages_disjoint U) hf.integrableOn using 1
    rw [passages_cover]
  · exact integral_add_compl hU.measurableSet hf

theorem integral_nonneg_of_passages {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ}
    (hf : Integrable f)
    (hpass : ∀ x ∈ U, 0 ≤ ∫ s in connectedComponentIn U x, f s)
    (hoff : ∀ s ∉ U, 0 ≤ f s) : 0 ≤ ∫ s, f s := by
  obtain ⟨hsum, heq⟩ := density_assembly hU hf
  have hpieces (J : Passages U) : 0 ≤ ∫ s in J.val, f s := by
    obtain ⟨x, hx, hxJ⟩ := J.property
    rw [hxJ]
    exact hpass x hx
  have hUpos : 0 ≤ ∫ s in U, f s := by
    rw [← hsum.tsum_eq]
    exact tsum_nonneg hpieces
  have hcomp : 0 ≤ ∫ s in Uᶜ, f s :=
    setIntegral_nonneg hU.measurableSet.compl hoff
  rw [← heq]
  exact add_nonneg hUpos hcomp

end ThreeManifold.GlobalAssembly

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.GlobalAssembly
open Set MeasureTheory Topology Function


theorem solution : type_of% @_root_.OAI.ThreeManifold.GlobalAssembly.integral_nonneg_of_passages := @_root_.OAI.ThreeManifold.GlobalAssembly.integral_nonneg_of_passages
