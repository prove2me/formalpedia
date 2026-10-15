-- Prove2me | solution 1 for OAI.DoublingHilbert.goodSheetPoint_exists_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:03:58.329003+00:00
-- url     : https://prove2.me/submissions/4e07516b-23a7-4fe7-bd1a-51bfcbe7723b

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Rectangles.lean:L380-L406
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.goodSheetPoint_exists_rectangle. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Theorems.Thm_OAI_DoublingHilbert_isOpen_sheetDomain

-- ---- from OAI.Geometry.DoublingHilbert.Integration ----
namespace OAI

/-! Line integration and global Lipschitz extensions of sheets. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

open MeasureTheory Set Filter
open scoped Topology

noncomputable section
namespace DoublingHilbert

section FTC
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end FTC

section MeanSquares
variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end MeanSquares
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology

section PartialIntegration
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end PartialIntegration
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
section Extensions
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
theorem globalSheet_eqOn {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) :
    EqOn (globalSheet hf w) (embeddingSheet f w) (sheetDomain w) := by
  obtain ⟨_, _, heq⟩ :=
    (exists_lipschitz_extension_finiteDimensional (embeddingSheet_lipschitz hf w)).choose_spec
  exact heq.symm

omit [CompleteSpace E] in
theorem column_globalSheet {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) {p : Base} (hp : p ∈ sheetDomain w) (v : Base) :
    column (globalSheet hf w) v p = sheetColumn (embeddingSheet f w) (sheetDomain w) v p := by
  have heq : globalSheet hf w =ᶠ[𝓝 p] embeddingSheet f w :=
    (isOpen_sheetDomain w).eventually_mem hp |>.mono fun q hq => globalSheet_eqOn hf w hq
  rw [column, heq.fderiv_eq]
  simp only [sheetColumn, Set.indicator_of_mem hp]

end Extensions
end
end DoublingHilbert

end

end OAI

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

theorem law_eq_closed (Q : Rectangle) : Q.law =
    (ENNReal.ofReal Q.area)⁻¹ • volume.restrict Q.closed := by
  simp only [law, Segment.law, restrict_Ioc_eq_restrict_Icc,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.prod_restrict,
    ← Measure.volume_eq_prod, area, closed, ENNReal.ofReal_mul Q.x.length_pos.le]
  rw [ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top), mul_comm]

theorem volume_closed (Q : Rectangle) : volume Q.closed = ENNReal.ofReal Q.area := by
  rw [closed, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
  exact (ENNReal.ofReal_mul Q.x.length_pos.le).symm

theorem integral_eq_average_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Rectangle) (g : Base → E) :
    (∫ p, g p ∂Q.law) = ⨍ p in Q.closed, g p := by
  rw [setAverage_eq', law_eq_closed, volume_closed]

theorem square_closed (p : Base) (r : ℝ) (hr : 0 < r) :
    (square p r hr).closed = Metric.closedBall p r := by
  rw [← Prod.eta p, ← closedBall_prod_same, Real.closedBall_eq_Icc, Real.closedBall_eq_Icc]
  rfl

end Rectangle

section LocalSquare
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
/-- Actual Lebesgue-good derivative points supply arbitrarily accurate base squares. -/
theorem goodSheetPoint_exists_rectangle {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) {w : Tuple} {p : Base} (hp : goodSheetPoint f w p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : Rectangle, Q.closed ⊆ sheetDomain w ∧
      (∫ q, ‖column (globalSheet hf w) (1, 0) q -
        sheetColumn (embeddingSheet f w) (sheetDomain w) (1, 0) p‖ ^ 2 ∂Q.law) < ε ∧
      (∫ q, ‖column (globalSheet hf w) (0, 1) q -
        sheetColumn (embeddingSheet f w) (sheetDomain w) (0, 1) p‖ ^ 2 ∂Q.law) < ε := by
  have he : ∀ᶠ r : ℝ in 𝓝[>] 0, Metric.closedBall p r ⊆ sheetDomain w :=
    (eventually_closedBall_subset ((isOpen_sheetDomain w).mem_nhds hp.1)).filter_mono
      nhdsWithin_le_nhds
  have hx := hp.2.2.1.eventually (gt_mem_nhds hε)
  have hy := hp.2.2.2.eventually (gt_mem_nhds hε)
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, hsub, hrx, hry⟩ := (hpos.and (he.and (hx.and hy))).exists
  refine ⟨Rectangle.square p r hr, ?_, ?_, ?_⟩
  · rwa [Rectangle.square_closed]
  · rw [Rectangle.integral_eq_average_closed, Rectangle.square_closed]
    refine lt_of_eq_of_lt ?_ hrx
    apply setAverage_congr_fun measurableSet_closedBall
    exact Eventually.of_forall fun q hq => by rw [column_globalSheet hf w (hsub hq)]
  · rw [Rectangle.integral_eq_average_closed, Rectangle.square_closed]
    refine lt_of_eq_of_lt ?_ hry
    apply setAverage_congr_fun measurableSet_closedBall
    exact Eventually.of_forall fun q hq => by rw [column_globalSheet hf w (hsub hq)]

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
open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
theorem solution {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) {w : Tuple} {p : Base} (hp : goodSheetPoint f w p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : Rectangle, Q.closed ⊆ sheetDomain w ∧
      (∫ q, ‖column (globalSheet hf w) (1, 0) q -
        sheetColumn (embeddingSheet f w) (sheetDomain w) (1, 0) p‖ ^ 2 ∂Q.law) < ε ∧
      (∫ q, ‖column (globalSheet hf w) (0, 1) q -
        sheetColumn (embeddingSheet f w) (sheetDomain w) (0, 1) p‖ ^ 2 ∂Q.law) < ε := by
  first
    | exact OAI.DoublingHilbert.goodSheetPoint_exists_rectangle hf hp hε
    | exact OAI.DoublingHilbert.goodSheetPoint_exists_rectangle
    | (apply OAI.DoublingHilbert.goodSheetPoint_exists_rectangle <;> assumption)
    | (intros; apply OAI.DoublingHilbert.goodSheetPoint_exists_rectangle <;> assumption)
