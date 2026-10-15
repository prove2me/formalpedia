-- Prove2me | solution 1 for OAI.DoublingHilbert.IsBoundedField.select
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:58:43.086356+00:00
-- url     : https://prove2.me/submissions/a306f126-1d84-4389-a7ee-832f611c9783

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Rectangles.lean:L167-L184
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.IsBoundedField.select. The node keeps its source
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

theorem select [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {g : I → X → E} (hg : ∀ i, IsBoundedField (g i))
    {σ : X → I} (hσ : Measurable σ) : IsBoundedField (fun p => g (σ p) p) := by
  classical
  choose M hM using fun i => (hg i).2
  have heq : (fun p => g (σ p) p) =
      fun p => ∑ i : I, {p | σ p = i}.indicator (g i) p := by
    funext p
    simp [Set.indicator_apply, eq_comm]
  refine ⟨?_, ∑ i, |M i|, fun p => ?_⟩
  · rw [heq]
    convert (Finset.stronglyMeasurable_sum Finset.univ fun i _ =>
      (hg i).1.indicator (hσ (measurableSet_singleton i))) using 1
    funext p
    simp only [Finset.sum_apply]
    rfl
  · exact (hM (σ p) p).trans ((le_abs_self _).trans
      (Finset.single_le_sum (fun i _ => abs_nonneg (M i)) (Finset.mem_univ _)))

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

end Segment

namespace Rectangle

end Rectangle
end
end DoublingHilbert

end

end OAI

-- ---- platform node ----
open OAI OAI.DoublingHilbert OAI.DoublingHilbert.IsBoundedField
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology
variable {X Y I E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E]

theorem solution [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {g : I → X → E} (hg : ∀ i, IsBoundedField (g i))
    {σ : X → I} (hσ : Measurable σ) : IsBoundedField (fun p => g (σ p) p) := by
  first
    | exact OAI.DoublingHilbert.IsBoundedField.select hg hσ
    | exact OAI.DoublingHilbert.IsBoundedField.select
    | (apply OAI.DoublingHilbert.IsBoundedField.select <;> assumption)
    | (intros; apply OAI.DoublingHilbert.IsBoundedField.select <;> assumption)
