-- Prove2me | solution 1 for OAI.SquareRootDegree.SmoothSelector.hat_local
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:24:40.330238+00:00
-- url     : https://prove2.me/submissions/a734c62f-f648-4889-9970-8dc5df04320c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/SmoothSelector.lean:L89-L104
-- (upload_full_project.md Phase 4): solution for node OAI.SquareRootDegree.SmoothSelector.hat_local. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothGaussian
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothSelector

-- ---- from OAI.Combinatorics.BooleanFunctions.SmoothSelector ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace SmoothSelector

theorem clip_of_nonpos {x : ℝ} (hx : x ≤ 0) : clip x = 0 := by
  unfold clip; rw [max_eq_left (le_trans (min_le_right _ _) hx)]
theorem clip_of_one_le {x : ℝ} (hx : 1 ≤ x) : clip x = 1 := by
  unfold clip; rw [min_eq_left hx, max_eq_right zero_le_one]

theorem hat_local {N : ℕ} {δ t : ℝ} {i : Fin (2*N+1)} (hδ : 0 < δ)
    (hi : hat N δ i t ≠ 0) : |center N δ i-(1+t)| < δ := by
  have hlo : -1 < t/δ+N-i := by
    by_contra hn
    have h : t/δ+N-i+1 ≤ 0 := by linarith
    have h' : t/δ+N-i ≤ 0 := by linarith
    exact hi (by simp [hat,clip_of_nonpos h,clip_of_nonpos h'])
  have hhi : t/δ+N-i < 1 := by
    by_contra hn
    have h : 1 ≤ t/δ+N-i := le_of_not_gt hn
    have h' : 1 ≤ t/δ+N-i+1 := by linarith
    exact hi (by simp [hat,clip_of_one_le h,clip_of_one_le h'])
  have hcancel : t/δ*δ = t := div_mul_cancel₀ _ hδ.ne'
  rw [abs_lt]
  dsimp [center]
  constructor <;> nlinarith [mul_pos hδ (sub_pos.mpr hlo),mul_pos hδ (sub_pos.mpr hhi)]

end SmoothSelector
end SquareRootDegree

end

end OAI

-- ---- platform node ----
open OAI OAI.SquareRootDegree OAI.SquareRootDegree.SmoothSelector
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

theorem solution {N : ℕ} {δ t : ℝ} {i : Fin (2*N+1)} (hδ : 0 < δ)
    (hi : hat N δ i t ≠ 0) : |center N δ i-(1+t)| < δ := by
  first
    | exact OAI.SquareRootDegree.SmoothSelector.hat_local hδ hi
    | exact OAI.SquareRootDegree.SmoothSelector.hat_local
    | (apply OAI.SquareRootDegree.SmoothSelector.hat_local <;> assumption)
    | (intros; apply OAI.SquareRootDegree.SmoothSelector.hat_local <;> assumption)
