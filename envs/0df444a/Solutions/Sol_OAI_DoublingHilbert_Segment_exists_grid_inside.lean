-- Prove2me | solution 1 for OAI.DoublingHilbert.Segment.exists_grid_inside
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:06:56.79158+00:00
-- url     : https://prove2.me/submissions/65a7d914-c218-471d-983d-ad4e9afa471c

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Grids.lean:L92-L127
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.Segment.exists_grid_inside. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids

-- ---- from OAI.Geometry.DoublingHilbert.Grids ----
namespace OAI

/-! Fine period grids, energy sampling, and sheet separation. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

namespace Segment

/-- Trim an interval to full grid periods, losing at most two periods. -/
theorem exists_grid_inside (I : Segment) {h : ℝ} (hh : 0 < h)
    (hsmall : h < I.length / 4) :
    ∃ (a : ℤ) (n : ℕ) (hn : 0 < n),
      I.lo ≤ (grid (a * h) h n hh hn).lo ∧
      (grid (a * h) h n hh hn).hi ≤ I.hi ∧
      I.length / 2 ≤ (grid (a * h) h n hh hn).length := by
  let a : ℤ := ⌈I.lo / h⌉
  let b : ℤ := ⌊I.hi / h⌋
  have ha₁ : I.lo ≤ (a : ℝ) * h := (div_le_iff₀ hh).mp (Int.le_ceil _)
  have ha₂ : (a : ℝ) * h < I.lo + h := by
    have := (mul_lt_mul_of_pos_right (Int.ceil_lt_add_one (I.lo / h)) hh)
    dsimp [a]
    nlinarith [div_mul_cancel₀ I.lo hh.ne']
  have hb₁ : (b : ℝ) * h ≤ I.hi := (le_div_iff₀ hh).mp (Int.floor_le _)
  have hb₂ : I.hi - h < (b : ℝ) * h := by
    have := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (I.hi / h)) hh
    dsimp [b]
    nlinarith [div_mul_cancel₀ I.hi hh.ne']
  have habr : (a : ℝ) < b := by
    have hlen := I.length_pos
    dsimp [length] at hsmall hlen
    nlinarith
  have hab : a < b := by exact_mod_cast habr
  let n := (b - a).toNat
  have hn : 0 < n := by dsimp [n]; omega
  have hncast : (n : ℝ) = (b : ℝ) - a := by
    have : (n : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  refine ⟨a, n, hn, ha₁, ?_, ?_⟩
  · change (a : ℝ) * h + n * h ≤ I.hi
    rw [hncast]
    nlinarith
  · rw [grid_length, hncast]
    dsimp [length] at hsmall ⊢
    nlinarith

end Segment

end
end DoublingHilbert

namespace DoublingHilbert
open Set Filter MeasureTheory
open scoped Topology
noncomputable section

namespace Segment

end Segment

namespace Rectangle

end Rectangle

end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
section SheetGeometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

end SheetGeometry

end
end DoublingHilbert

end OAI

-- ---- platform node ----
open OAI OAI.DoublingHilbert OAI.DoublingHilbert.Segment
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter
open scoped Topology

theorem solution (I : Segment) {h : ℝ} (hh : 0 < h)
    (hsmall : h < I.length / 4) :
    ∃ (a : ℤ) (n : ℕ) (hn : 0 < n),
      I.lo ≤ (grid (a * h) h n hh hn).lo ∧
      (grid (a * h) h n hh hn).hi ≤ I.hi ∧
      I.length / 2 ≤ (grid (a * h) h n hh hn).length := by
  first
    | exact OAI.DoublingHilbert.Segment.exists_grid_inside I hh hsmall
    | exact OAI.DoublingHilbert.Segment.exists_grid_inside
    | (apply OAI.DoublingHilbert.Segment.exists_grid_inside <;> assumption)
    | (intros; apply OAI.DoublingHilbert.Segment.exists_grid_inside <;> assumption)
