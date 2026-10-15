-- Prove2me | solution 1 for OAI.DoublingHilbert.Rectangle.integral_le_four_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:02:43.131055+00:00
-- url     : https://prove2.me/submissions/f99f8294-0ae3-4961-a99d-92007bca2cfa

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Rectangles.lean:L347-L364
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.Rectangle.integral_le_four_of_subset. The node keeps its source
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

theorem area_pos (Q : Rectangle) : 0 < Q.area := mul_pos Q.x.length_pos Q.y.length_pos

theorem law_eq_closed (Q : Rectangle) : Q.law =
    (ENNReal.ofReal Q.area)⁻¹ • volume.restrict Q.closed := by
  simp only [law, Segment.law, restrict_Ioc_eq_restrict_Icc,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.prod_restrict,
    ← Measure.volume_eq_prod, area, closed, ENNReal.ofReal_mul Q.x.length_pos.le]
  rw [ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top), mul_comm]

theorem volume_closed (Q : Rectangle) : volume Q.closed = ENNReal.ofReal Q.area := by
  rw [closed, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
  exact (ENNReal.ofReal_mul Q.x.length_pos.le).symm

theorem integral_eq_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Rectangle) (g : Base → E) :
    (∫ p, g p ∂Q.law) = Q.area⁻¹ • ∫ p in Q.closed, g p := by
  rw [law_eq_closed, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal Q.area_pos.le]

theorem area_mul_integral (Q : Rectangle) (g : Base → ℝ) :
    Q.area * (∫ p, g p ∂Q.law) = ∫ p in Q.closed, g p := by
  rw [Q.integral_eq_closed, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ Q.area_pos.ne', one_mul]

/-- Trimming at most half of each side increases a nonnegative mean by at most four. -/
theorem integral_le_four_of_subset (P Q : Rectangle) {g : Base → ℝ}
    (hg : IsBoundedField g) (hpos : ∀ p, 0 ≤ g p)
    (hsub : Q.closed ⊆ P.closed)
    (hx : P.x.length / 2 ≤ Q.x.length) (hy : P.y.length / 2 ≤ Q.y.length) :
    (∫ p, g p ∂Q.law) ≤ 4 * (∫ p, g p ∂P.law) := by
  have : IsFiniteMeasure (volume.restrict P.closed) :=
    isFiniteMeasure_restrict.mpr (by rw [P.volume_closed]; exact ENNReal.ofReal_ne_top)
  have hi := setIntegral_mono_set (s := Q.closed) (t := P.closed) (hg.integrable (volume.restrict P.closed))
    (Eventually.of_forall hpos) (Eventually.of_forall hsub)
  rw [← Q.area_mul_integral g, ← P.area_mul_integral g] at hi
  have ha : P.area ≤ 4 * Q.area := by
    have := mul_le_mul hx hy (div_nonneg P.y.length_pos.le (by norm_num)) Q.x.length_pos.le
    dsimp [area]
    nlinarith
  have hpmean : 0 ≤ (∫ p, g p ∂P.law) := integral_nonneg hpos
  have hmul := mul_le_mul_of_nonneg_right ha hpmean
  nlinarith [Q.area_pos]

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

end Segment

namespace Rectangle

end Rectangle
end
end DoublingHilbert

end

end OAI

-- ---- platform node ----
open OAI OAI.DoublingHilbert OAI.DoublingHilbert.Rectangle
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology

theorem solution (P Q : Rectangle) {g : Base → ℝ}
    (hg : IsBoundedField g) (hpos : ∀ p, 0 ≤ g p)
    (hsub : Q.closed ⊆ P.closed)
    (hx : P.x.length / 2 ≤ Q.x.length) (hy : P.y.length / 2 ≤ Q.y.length) :
    (∫ p, g p ∂Q.law) ≤ 4 * (∫ p, g p ∂P.law) := by
  first
    | exact OAI.DoublingHilbert.Rectangle.integral_le_four_of_subset P Q hg hpos hsub hx hy
    | exact OAI.DoublingHilbert.Rectangle.integral_le_four_of_subset
    | (apply OAI.DoublingHilbert.Rectangle.integral_le_four_of_subset <;> assumption)
    | (intros; apply OAI.DoublingHilbert.Rectangle.integral_le_four_of_subset <;> assumption)
