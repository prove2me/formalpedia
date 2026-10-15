-- Prove2me | solution 1 for OAI.Paper092.mem_standardSimplex_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:28:50.655383+00:00
-- url     : https://prove2.me/submissions/822a46a3-f5d7-4235-91b4-fbe0721c645e

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/SimplexCoordinates.lean:L13-L58
-- (upload_full_project.md Phase 4): solution for node OAI.Paper092.mem_standardSimplex_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ProjectionVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexGeometry

-- ---- from OAI.Geometry.ProjectionVolume.SimplexCoordinates ----
namespace OAI

noncomputable section

open Set
open scoped BigOperators

namespace Paper092

theorem mem_standardSimplex_iff {n : ℕ} (x : Euclidean n) :
    x ∈ standardSimplex n ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1 := by
  constructor
  · intro hx
    have hsubset : standardSimplex n ⊆
        {y : Euclidean n | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1} := by
      apply convexHull_min
      · rintro y (rfl | ⟨i, rfl⟩)
        · simp
        · constructor
          · intro j
            simp only [PiLp.single_apply]
            split_ifs <;> norm_num
          · simp [PiLp.single_apply]
      · intro u hu v hv a b ha hb hab
        constructor
        · intro i
          change 0 ≤ a * u i + b * v i
          exact add_nonneg (mul_nonneg ha (hu.1 i)) (mul_nonneg hb (hv.1 i))
        · change ∑ i, (a * u i + b * v i) ≤ 1
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          calc
            a * ∑ i, u i + b * ∑ i, v i ≤ a * 1 + b * 1 :=
              add_le_add (mul_le_mul_of_nonneg_left hu.2 ha)
                (mul_le_mul_of_nonneg_left hv.2 hb)
            _ = 1 := by simpa using hab
    exact hsubset hx
  · rintro ⟨hpos, hsum⟩
    let w : Option (Fin n) → ℝ
      | none => 1 - ∑ i, x i
      | some i => x i
    let v : Option (Fin n) → Euclidean n
      | none => 0
      | some i => EuclideanSpace.single i 1
    refine mem_convexHull_of_exists_fintype w v ?_ ?_ ?_ ?_
    · intro i
      cases i with
      | none => exact sub_nonneg.mpr hsum
      | some i => exact hpos i
    · simp [w, Fintype.sum_option]
    · intro i
      cases i with
      | none => exact mem_insert 0 _
      | some i => exact mem_insert_of_mem 0 (mem_range_self i)
    · ext j
      simp [w, v, Fintype.sum_option, Pi.single_apply]

end Paper092

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper092
open Set
open scoped BigOperators

theorem solution {n : ℕ} (x : Euclidean n) :
    x ∈ standardSimplex n ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1 := by
  first
    | exact OAI.Paper092.mem_standardSimplex_iff x
    | exact OAI.Paper092.mem_standardSimplex_iff
    | (apply OAI.Paper092.mem_standardSimplex_iff <;> assumption)
    | (intros; apply OAI.Paper092.mem_standardSimplex_iff <;> assumption)
