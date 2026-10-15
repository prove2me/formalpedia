-- Prove2me | solution 1 for OAI.DoublingHilbert.Segment.integral_grid
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:05:42.106236+00:00
-- url     : https://prove2.me/submissions/e5f57e36-ef42-414c-b32c-871386ae44d3

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Rectangles.lean:L433-L449
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.Segment.integral_grid. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles

-- ---- from OAI.Geometry.DoublingHilbert.Rectangles ----
namespace OAI

/-! Rectangle probability measures, transport estimates, and finite averaging. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace DoublingHilbert

namespace Segment

theorem integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Segment) (g : ℝ → E) :
    (∫ x, g x ∂I.law) = I.length⁻¹ • ∫ x in I.lo..I.hi, g x := by
  rw [law, integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofReal I.length_pos.le,
    intervalIntegral.integral_of_le I.lt.le]

theorem integrable_iff {E : Type*} [NormedAddCommGroup E]
    (I : Segment) {g : ℝ → E} :
    Integrable g I.law ↔ IntervalIntegrable g volume I.lo I.hi := by
  rw [law, integrable_smul_measure
    (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr I.length_pos)),
    intervalIntegrable_iff_integrableOn_Ioc_of_le I.lt.le]
  rfl

end Segment

namespace Rectangle

end Rectangle

section BoundedFields
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

namespace IsBoundedField

theorem integrable {g : X → E} (hg : IsBoundedField g) (μ : Measure X)
    [IsFiniteMeasure μ] : Integrable g μ := by
  obtain ⟨M, hM⟩ := hg.2
  exact Integrable.of_bound hg.1.aestronglyMeasurable M (Eventually.of_forall hM)

end IsBoundedField
end BoundedFields

end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology

namespace Rectangle

end Rectangle

namespace IsBoundedField
variable {X Y I E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E]

variable [NormedSpace ℝ E]

end IsBoundedField
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

section RectangleFTC
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end RectangleFTC
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace Rectangle

end Rectangle

section LocalSquare
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end LocalSquare
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

namespace Segment

/-- Exact finite averaging over adjacent equal cells. -/
theorem integral_grid {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a h : ℝ) {n : ℕ} (hh : 0 < h) (hn : 0 < n) {g : ℝ → E}
    (hg : IsBoundedField g) :
    (∫ x, g x ∂(grid a h n hh hn).law) =
      (n : ℝ)⁻¹ • ∑ i : Fin n, ∫ x, g x ∂(cell a h hh i).law := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ => a + i * h) (n := n) (f := g) (μ := volume)
    (fun i _ => (cell a h hh i).integrable_iff.mp (hg.integrable _))
  simp only [Nat.cast_zero, zero_mul, add_zero] at hsum
  rw [← Fin.sum_univ_eq_sum_range] at hsum
  simp_rw [integral_eq, grid_length, cell_length]
  rw [← Finset.smul_sum, smul_smul]
  have hs : (n : ℝ)⁻¹ * h⁻¹ = ((n : ℝ) * h)⁻¹ := by ring
  rw [hs]
  congr 1
  exact hsum.symm

end Segment

namespace Rectangle

end Rectangle
end
end DoublingHilbert

end

end OAI

-- ---- platform node ----
open OAI OAI.DoublingHilbert OAI.DoublingHilbert.Segment
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a h : ℝ) {n : ℕ} (hh : 0 < h) (hn : 0 < n) {g : ℝ → E}
    (hg : IsBoundedField g) :
    (∫ x, g x ∂(grid a h n hh hn).law) =
      (n : ℝ)⁻¹ • ∑ i : Fin n, ∫ x, g x ∂(cell a h hh i).law := by
  first
    | exact OAI.DoublingHilbert.Segment.integral_grid a h hh hn hg
    | exact OAI.DoublingHilbert.Segment.integral_grid
    | (apply OAI.DoublingHilbert.Segment.integral_grid <;> assumption)
    | (intros; apply OAI.DoublingHilbert.Segment.integral_grid <;> assumption)
