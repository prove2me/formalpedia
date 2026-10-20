-- Prove2me | solution 1 for OAI.EuclideanRamsey.CircleConsequence.circle_five_affineSpan
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:45:27.810816+00:00
-- url     : https://prove2.me/submissions/984a6350-8b05-432a-80bb-fdbe13b6105c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/CircleSpan.lean:L7-L44
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.CircleConsequence.circle_five_affineSpan. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleInterpolation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleRows
import Theorems.Thm_OAI_EuclideanRamsey_CircleConsequence_secantValue_ne_zero

-- ---- from OAI.Combinatorics.EuclideanRamsey.CircleGeometry ----
namespace OAI

noncomputable section
namespace EuclideanRamsey.CircleConsequence

/-- The metric circle equation implies the scalar coordinate equation. -/
theorem circle_coordinates {s : ℕ} (a : Fin s → Space 2)
    (c : Space 2) (r : ℝ) (hc : ∀ i, dist (a i) c = r) :
    ∀ i, (a i 0-c 0)^2 + (a i 1-c 1)^2 = r^2 := by
  intro i
  have h := congrArg (fun x : ℝ => x^2) (hc i)
  simpa [dist_eq_norm, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two,
    Real.norm_eq_abs, sq_abs] using h

end EuclideanRamsey.CircleConsequence

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.CircleSpan ----
namespace OAI
noncomputable section
namespace EuclideanRamsey.CircleConsequence

/-- Three actual distinct circle points already affinely span the plane.
The inverse two-by-two determinant is written explicitly. -/
theorem circle_five_affineSpan (a : Fin 5 → Space 2)
    (ha : Function.Injective a) (c : Space 2) (r : ℝ)
    (hc : ∀ i, dist (a i) c = r) : affineSpan ℝ (Set.range a) = ⊤ := by
  classical
  let A := affineSpan ℝ (Set.range a)
  have hp (i : Fin 5) : a i ∈ A := mem_affineSpan ℝ (Set.mem_range_self i)
  let u := a 1 - a 0
  let v := a 2 - a 0
  let D : ℝ := u 0 * v 1 - v 0 * u 1
  have hfield := secantValue_ne_zero a ha c (r^2) (circle_coordinates a c r hc)
    0 1 2 (by decide) (by decide) (by decide)
  have hD : D ≠ 0 := by
    intro h
    apply hfield
    apply Subtype.ext
    simpa [D, u, v, secantValue, coordinate, mul_comm] using h
  have hu : u ∈ A.direction := by
    simpa [u, vsub_eq_sub] using AffineSubspace.vsub_mem_direction (hp 1) (hp 0)
  have hv : v ∈ A.direction := by
    simpa [v, vsub_eq_sub] using AffineSubspace.vsub_mem_direction (hp 2) (hp 0)
  apply top_unique
  intro x hx
  let w := x - a 0
  let α : ℝ := (w 0 * v 1 - v 0 * w 1) / D
  let β : ℝ := (u 0 * w 1 - w 0 * u 1) / D
  have hcomb : α • u + β • v = w := by
    ext j
    fin_cases j <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;>
      dsimp [α, β] <;>
      field_simp [hD] <;>
      dsimp [D] <;> ring
  have hm : α • u + β • v ∈ A.direction :=
    A.direction.add_mem (A.direction.smul_mem α hu) (A.direction.smul_mem β hv)
  have he := AffineSubspace.vadd_mem_of_mem_direction hm (hp 0)
  simpa [hcomb, w, vadd_eq_add] using he
end EuclideanRamsey.CircleConsequence

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.CircleConsequence


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.CircleConsequence.circle_five_affineSpan := @_root_.OAI.EuclideanRamsey.CircleConsequence.circle_five_affineSpan
