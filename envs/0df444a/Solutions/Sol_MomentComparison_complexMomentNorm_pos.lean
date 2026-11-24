-- Prove2me | solution 1 for MomentComparison.complexMomentNorm_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:16:08.415716+00:00
-- url     : https://prove2.me/submissions/eb95bb4c-e6e6-4b4d-bf67-00966c1387f5

module
public import Definitions.Def_MomentComparison_Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_MomentNorm
public import Theorems.Thm_MomentComparison_cubeAverage_pos

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison
namespace MomentComparison
theorem _root_.solution {n : ℕ} (p : ℝ) {f : Cube n → ℂ}
    (hf : ∃ x, f x ≠ 0) : 0 < complexMomentNorm p f := by
  obtain ⟨x, hx⟩ := hf
  exact Real.rpow_pos_of_pos (cubeAverage_pos
    (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    ⟨x, Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) _⟩) _
end MomentComparison
