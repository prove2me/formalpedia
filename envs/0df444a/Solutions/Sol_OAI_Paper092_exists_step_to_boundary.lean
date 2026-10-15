-- Prove2me | solution 1 for OAI.Paper092.exists_step_to_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:30:17.78379+00:00
-- url     : https://prove2.me/submissions/5b1e4e57-0b04-4d05-911b-6387787baab6

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/SimplexProjection.lean:L51-L73
-- (upload_full_project.md Phase 4): solution for node OAI.Paper092.exists_step_to_boundary. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ProjectionVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexProjection

-- ---- from OAI.Geometry.ProjectionVolume.SimplexProjection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

open Set MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace Paper092

theorem exists_step_to_boundary {ι : Type uι} [Fintype ι] (q v : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hv : ∃ i, v i < 0) :
    ∃ t : ℝ, 0 ≤ t ∧ (∀ i, 0 ≤ q i + t * v i) ∧
      ∃ i, v i < 0 ∧ q i + t * v i = 0 := by
  classical
  let s := Finset.univ.filter (fun i => v i < 0)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hv
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image s (fun j => q j / (-v j)) hs
  have hi0 : v i < 0 := (Finset.mem_filter.mp hi).2
  have hneg : 0 < -v i := neg_pos.mpr hi0
  have ht : 0 ≤ q i / (-v i) := div_nonneg (hq i) hneg.le
  have heq : q i + q i / (-v i) * v i = 0 := by
    have hmul := div_mul_cancel₀ (q i) (ne_of_gt hneg)
    linarith
  refine ⟨q i / (-v i), ht, ?_, i, hi0, heq⟩
  intro j
  by_cases hj : v j < 0
  · have hjmem : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
    have hle := (le_div_iff₀ (neg_pos.mpr hj)).mp (hmin j hjmem)
    linarith
  · exact add_nonneg (hq j) (mul_nonneg ht (le_of_not_gt hj))

end Paper092

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper092
universe uι
open Set MeasureTheory
open scoped RealInnerProductSpace

theorem solution {ι : Type uι} [Fintype ι] (q v : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hv : ∃ i, v i < 0) :
    ∃ t : ℝ, 0 ≤ t ∧ (∀ i, 0 ≤ q i + t * v i) ∧
      ∃ i, v i < 0 ∧ q i + t * v i = 0 := by
  first
    | exact OAI.Paper092.exists_step_to_boundary q v hq hv
    | exact OAI.Paper092.exists_step_to_boundary
    | (apply OAI.Paper092.exists_step_to_boundary <;> assumption)
    | (intros; apply OAI.Paper092.exists_step_to_boundary <;> assumption)
