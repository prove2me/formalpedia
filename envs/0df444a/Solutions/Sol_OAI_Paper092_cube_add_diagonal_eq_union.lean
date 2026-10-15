-- Prove2me | solution 1 for OAI.Paper092.cube_add_diagonal_eq_union
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:55:37.881153+00:00
-- url     : https://prove2.me/submissions/998d2e77-75ea-4cc4-b151-bd4aed18e676

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/Extrusion.lean:L154-L205
-- (upload_full_project.md Phase 4): solution for node OAI.Paper092.cube_add_diagonal_eq_union. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ProjectionVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_FacetAreas
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductVolumeGeneral
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductFacetAreas
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProjectionJacobian
import Definitions.Def_OAI_Geometry_ProjectionVolume_SupportGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_Extrusion

-- ---- from OAI.Geometry.ProjectionVolume.Extrusion ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

open Set MeasureTheory
open scoped ENNReal Pointwise

namespace Paper092

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem cube_add_diagonal_eq_union [Nonempty ι] :
    unitCube ι + segment ℝ (0 : ι → ℝ) 1 =
      unitCube ι ∪ ⋃ i, extrusionCell i := by
  ext x
  constructor
  · rintro ⟨q, hq, z, hz, rfl⟩
    change (∀ i, 0 ≤ q i) ∧ (∀ i, q i ≤ 1) at hq
    rw [segment_eq_image] at hz
    rcases hz with ⟨t, ht, rfl⟩
    simp only [smul_zero, zero_add]
    by_cases hmax : ∀ i, q i + t ≤ 1
    · left
      constructor <;> intro i
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
        exact add_nonneg (hq.1 i) ht.1
      · simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
          using hmax i
    · right
      obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ q Finset.univ_nonempty
      refine mem_iUnion.mpr ⟨i, ?_⟩
      push Not at hmax
      obtain ⟨j, hj⟩ := hmax
      have hji := hi j (Finset.mem_univ j)
      constructor
      · constructor
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
          linarith
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
          linarith [hq.2 i, ht.2]
      · intro k _
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
        constructor
        · linarith [hq.2 i, hq.1 k]
        · linarith [hi k (Finset.mem_univ k)]
  · rintro (hx | hx)
    · exact ⟨x, hx, 0, left_mem_segment ℝ _ _, add_zero x⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      refine ⟨fun j => x j - (x i - 1), ?_, (x i - 1) • (1 : ι → ℝ), ?_, ?_⟩
      · constructor <;> intro j
        · change 0 ≤ x j - (x i - 1)
          by_cases hj : j = i
          · subst j; linarith
          · linarith [(hi.2 j hj).1]
        · change x j - (x i - 1) ≤ 1
          by_cases hj : j = i
          · subst j; linarith
          · linarith [(hi.2 j hj).2]
      · rw [segment_eq_image]
        refine ⟨x i - 1, ⟨by linarith [hi.1.1], by linarith [hi.1.2]⟩, ?_⟩
        simp
      · ext j
        simp

end Paper092

end OAI

-- ---- platform node ----
open OAI OAI.Paper092
universe uι
open Set MeasureTheory
open scoped ENNReal Pointwise
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem solution [Nonempty ι] :
    unitCube ι + segment ℝ (0 : ι → ℝ) 1 =
      unitCube ι ∪ ⋃ i, extrusionCell i := by
  first
    | exact OAI.Paper092.cube_add_diagonal_eq_union
    | (apply OAI.Paper092.cube_add_diagonal_eq_union <;> assumption)
    | (intros; apply OAI.Paper092.cube_add_diagonal_eq_union <;> assumption)
