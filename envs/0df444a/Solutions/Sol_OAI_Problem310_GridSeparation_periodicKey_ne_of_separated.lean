-- Prove2me | solution 1 for OAI.Problem310.GridSeparation.periodicKey_ne_of_separated
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:29:17.82948+00:00
-- url     : https://prove2.me/submissions/ff482dee-5b9b-4242-af86-d43fd9462a35

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/GridSeparation.lean:L21-L46
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.GridSeparation.periodicKey_ne_of_separated. The node keeps its source
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

/-- Points separated by at least one grid mesh in both circular directions
cannot have the same periodic key. This includes points on cell boundaries. -/
lemma periodicKey_ne_of_separated {q x y : ℝ} (hq : 0 < q)
    (hlo : 1 ≤ q * (y - x)) (hhi : q * (y - x) ≤ q - 1) :
    periodicKey q x ≠ periodicKey q y := by
  intro heq
  have hxlo := Int.floor_le (q * Int.fract x)
  have hxhi := Int.lt_floor_add_one (q * Int.fract x)
  have hylo := Int.floor_le (q * Int.fract y)
  have hyhi := Int.lt_floor_add_one (q * Int.fract y)
  change ⌊q * Int.fract x⌋ = ⌊q * Int.fract y⌋ at heq
  have hcast : (⌊q * Int.fract x⌋ : ℝ) = (⌊q * Int.fract y⌋ : ℝ) :=
    congrArg (fun n : ℤ => (n : ℝ)) heq
  have hdifflo : -1 < q * (Int.fract y - Int.fract x) := by nlinarith
  have hdiffhi : q * (Int.fract y - Int.fract x) < 1 := by nlinarith
  have hx := Int.floor_add_fract x
  have hy := Int.floor_add_fract y
  let k : ℤ := ⌊y⌋ - ⌊x⌋
  have hk : (k : ℝ) = y - x - (Int.fract y - Int.fract x) := by
    simp only [k, Int.cast_sub]
    linarith
  have hkpos : 0 < (k : ℝ) := by nlinarith
  have hklt : (k : ℝ) < 1 := by nlinarith
  have hkpos' : (0 : ℤ) < k := by exact_mod_cast hkpos
  have hklt' : k < (1 : ℤ) := by exact_mod_cast hklt
  omega

end Problem310.GridSeparation

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.GridSeparation


theorem solution : type_of% @_root_.OAI.Problem310.GridSeparation.periodicKey_ne_of_separated := @_root_.OAI.Problem310.GridSeparation.periodicKey_ne_of_separated
