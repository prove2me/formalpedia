-- Prove2me | solution 1 for OAI.Problem310.GridSeparation.periodicKey_dyadic_refine
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:32:51.374989+00:00
-- url     : https://prove2.me/submissions/861efd9b-3f3b-4ad9-9ce9-424d80c88afc

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/GridSeparation.lean:L154-L169
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.GridSeparation.periodicKey_dyadic_refine. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation

-- ---- from OAI.MeasureTheory.DyadicAvoidance.GridSeparation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_α

noncomputable section

namespace Problem310.GridSeparation

/-- The nesting identity for the periodic dyadic grids. -/
lemma periodicKey_dyadic_refine {b B : ℕ} (hb : b ≤ B) (x : ℝ) :
    periodicKey ((2 : ℝ) ^ (b + 2)) x =
      periodicKey ((2 : ℝ) ^ (B + 2)) x / (2 : ℤ) ^ (B - b) := by
  have heq : (2 : ℝ) ^ (B + 2) * Int.fract x =
      ((2 : ℝ) ^ (b + 2) * Int.fract x) * ((2 ^ (B - b) : ℕ) : ℝ) := by
    push_cast
    rw [mul_right_comm, ← pow_add]
    congr 1
    congr 1
    omega
  unfold periodicKey
  rw [heq]
  simpa using (Int.mul_natCast_floor_div_cancel
    (n := 2 ^ (B - b)) (by positivity)
    ((2 : ℝ) ^ (b + 2) * Int.fract x)).symm

end Problem310.GridSeparation

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.GridSeparation


theorem solution : type_of% @_root_.OAI.Problem310.GridSeparation.periodicKey_dyadic_refine := @_root_.OAI.Problem310.GridSeparation.periodicKey_dyadic_refine
