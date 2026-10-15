-- Prove2me | solution 1 for OAI.DoublingHilbert.exists_vertical_line
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:38:11.199696+00:00
-- url     : https://prove2.me/submissions/83dcafdd-1e21-4315-b983-49e51ba355fb

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Crossings.lean:L147-L182
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.exists_vertical_line. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
import Theorems.Thm_OAI_DoublingHilbert_oscillation_sq_le_segment_energy

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

/-- Vector-valued FTC for a Lipschitz curve with its a.e. derivative specified.
This is the scalar absolutely-continuous FTC tested against the continuous dual. -/
theorem integral_eq_sub_of_lipschitz_ae_derivative
    {f g : ℝ → E} {a b : ℝ} {C : NNReal}
    (hf : LipschitzOnWith C f (uIcc a b))
    (hg : IntervalIntegrable g volume a b)
    (hderiv : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (g x) x) :
    (∫ x in a..b, g x) = f b - f a := by
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun L => ?_
  rw [← L.intervalIntegral_comp_comm hg, L.map_sub]
  have hAC := (L.lipschitz.comp_lipschitzOnWith hf).absolutelyContinuousOnInterval
  calc
    (∫ x in a..b, L (g x)) = ∫ x in a..b, deriv (L ∘ f) x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hderiv] with x hx hxab
      have h'x := L.hasFDerivAt.comp_hasDerivAt x (hx (uIoc_subset_uIcc hxab))
      exact h'x.deriv.symm
    _ = L (f b) - L (f a) := hAC.integral_deriv_eq_sub

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

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem norm_column_le {f : ℝ × ℝ → E} {C : NNReal} (hf : LipschitzWith C f)
    (v : ℝ × ℝ) (p : ℝ × ℝ) : ‖column f v p‖ ≤ C * ‖v‖ :=
  ((fderiv ℝ f p).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg v))

omit [CompleteSpace E] in
theorem stronglyMeasurable_column (f : ℝ × ℝ → E) (v : ℝ × ℝ) :
    StronglyMeasurable (column f v) := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  exact ((ContinuousLinearMap.apply ℝ E v).continuous.measurable.comp
    (measurable_fderiv ℝ f)).stronglyMeasurable

omit [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem intervalIntegrable_of_bound {g : ℝ → E} (hg : AEStronglyMeasurable g volume)
    {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (a b : ℝ) : IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff']
  exact IntegrableOn.of_bound isCompact_uIcc.measure_lt_top hg.restrict M
    (Eventually.of_forall hM)

omit [CompleteSpace E] in
theorem intervalIntegrable_column_y {f : ℝ × ℝ → E} {C : NNReal} (hf : LipschitzWith C f)
    (v : ℝ × ℝ) (x a b : ℝ) :
    IntervalIntegrable (fun y => column f v (x, y)) volume a b := by
  apply intervalIntegrable_of_bound
    ((stronglyMeasurable_column f v).comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  intro y
  exact norm_column_le hf v (x, y)

omit [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem lipschitz_line_y {f : ℝ × ℝ → E} {C : NNReal} (hf : LipschitzWith C f) (x : ℝ) :
    LipschitzWith C (fun y => f (x, y)) := by
  apply LipschitzWith.of_dist_le_mul
  intro y y'
  simpa only [dist_prod_same_left] using hf.dist_le_mul (x, y) (x, y')

omit [CompleteSpace E] in
theorem ae_line_derivative_y {f : ℝ × ℝ → E} {C : NNReal} (hf : LipschitzWith C f) :
    ∀ᵐ x, ∀ᵐ y, HasDerivAt (fun t => f (x, t)) (column f (0, 1) (x, y)) y := by
  have hd := hf.ae_differentiableAt (μ := (volume : Measure (ℝ × ℝ)))
  rw [Measure.volume_eq_prod] at hd
  filter_upwards [Measure.ae_ae_of_ae_prod hd] with x hx
  filter_upwards [hx] with y hy
  exact hy.hasFDerivAt.comp_hasDerivAt y ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))

/-- The corresponding vertical-line identity. -/
theorem ae_integral_column_y {f : ℝ × ℝ → E} {C : NNReal} (hf : LipschitzWith C f) :
    ∀ᵐ x, ∀ a b : ℝ, (∫ y in a..b, column f (0, 1) (x, y)) = f (x, b) - f (x, a) := by
  filter_upwards [ae_line_derivative_y hf] with x hx
  intro a b
  exact integral_eq_sub_of_lipschitz_ae_derivative (lipschitz_line_y hf x).lipschitzOnWith
    (intervalIntegrable_column_y hf (0, 1) x a b) (hx.mono fun _ h _ => h)

end PartialIntegration
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
section Extensions
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

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

theorem ae_iff (I : Segment) {P : ℝ → Prop} :
    (∀ᵐ x ∂I.law, P x) ↔ ∀ᵐ x, x ∈ Ioc I.lo I.hi → P x := by
  rw [law, Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top),
    ae_restrict_iff' measurableSet_Ioc]

theorem ae_mem (I : Segment) : ∀ᵐ x ∂I.law, x ∈ Ioo I.lo I.hi := by
  rw [I.ae_iff]
  filter_upwards [volume.ae_ne I.hi] with x hx hmem
  exact ⟨hmem.1, lt_of_le_of_ne hmem.2 hx⟩

theorem ae_of_ae (I : Segment) {P : ℝ → Prop} (hP : ∀ᵐ x, P x) :
    ∀ᵐ x ∂I.law, P x := I.ae_iff.mpr (hP.mono fun _ hx _ => hx)

end Segment

namespace Rectangle

theorem integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Rectangle) (g : ℝ × ℝ → E) (hg : Integrable g Q.law) :
    (∫ p, g p ∂Q.law) = ∫ x, ∫ y, g (x, y) ∂Q.y.law ∂Q.x.law :=
  integral_prod g hg

end Rectangle

section BoundedFields
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

namespace IsBoundedField

theorem integrable {g : X → E} (hg : IsBoundedField g) (μ : Measure X)
    [IsFiniteMeasure μ] : Integrable g μ := by
  obtain ⟨M, hM⟩ := hg.2
  exact Integrable.of_bound hg.1.aestronglyMeasurable M (Eventually.of_forall hM)

theorem norm_sq {g : X → E} (hg : IsBoundedField g) :
    IsBoundedField (fun x => ‖g x‖ ^ 2) := by
  obtain ⟨M, hM⟩ := hg.2
  refine ⟨hg.1.norm.pow 2, M ^ 2, fun x => ?_⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hM x) 2

theorem sub {f g : X → E} (hf : IsBoundedField f) (hg : IsBoundedField g) :
    IsBoundedField (fun x => f x - g x) := by
  obtain ⟨M, hM⟩ := hf.2
  obtain ⟨N, hN⟩ := hg.2
  exact ⟨hf.1.sub hg.1, M + N, fun x => (norm_sub_le _ _).trans (add_le_add (hM x) (hN x))⟩

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

theorem comp_measurable {g : X → E} (hg : IsBoundedField g) {f : Y → X}
    (hf : Measurable f) : IsBoundedField (g ∘ f) :=
  ⟨hg.1.comp_measurable hf, by obtain ⟨M, hM⟩ := hg.2; exact ⟨M, fun y => hM (f y)⟩⟩

variable [NormedSpace ℝ E]

theorem integral_snd {g : X × Y → E} (hg : IsBoundedField g) (ν : Measure Y)
    [IsProbabilityMeasure ν] : IsBoundedField (fun x => ∫ y, g (x, y) ∂ν) := by
  obtain ⟨M, hM⟩ := hg.2
  refine ⟨hg.1.integral_prod_right', M, fun x => ?_⟩
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall fun y => hM (x, y))

end IsBoundedField
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

section RectangleFTC
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
theorem boundedField_column {f : Base → E} {C : NNReal} (hf : LipschitzWith C f)
    (v : Base) : IsBoundedField (column f v) :=
  ⟨stronglyMeasurable_column f v, C * ‖v‖, norm_column_le hf v⟩

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

end Segment

end
end DoublingHilbert

namespace DoublingHilbert
open Set Filter MeasureTheory
open scoped Topology
noncomputable section

/-- First-moment sampling avoiding every specified null exceptional set. -/
theorem exists_good_le_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {g : X → ℝ} (hg : Integrable g μ)
    {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∃ x, P x ∧ g x ≤ ∫ y, g y ∂μ := by
  obtain ⟨x, hx, hbound⟩ := exists_notMem_null_le_integral hg (ae_iff.mp hP)
  exact ⟨x, by simpa using hx, hbound⟩

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

-- ---- from OAI.Geometry.DoublingHilbert.SelectedSheets ----
namespace OAI

/-! Periodic selections of sheets and stripewise derivative means. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

namespace IsBoundedField
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

theorem const_mul {g : X → ℝ} (hg : IsBoundedField g) (r : ℝ) :
    IsBoundedField (fun x => r * g x) := by
  obtain ⟨M, hM⟩ := hg.2
  refine ⟨hg.1.const_mul r, ‖r‖ * M, fun x => ?_⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg r)

end IsBoundedField

section StripeMeans
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

end StripeMeans
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

namespace PeriodGrid
variable {j : ℕ}

end PeriodGrid

end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

namespace Rectangle

end Rectangle

section SelectedSheets
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end SelectedSheets
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section
section VerticalStripeMean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end VerticalStripeMean
end
end DoublingHilbert

end OAI

-- ---- from OAI.Geometry.DoublingHilbert.Crossings ----
namespace OAI

open MeasureTheory Set Filter
open scoped BigOperators Topology

open Metric

/-! Selected period crossings and finite-dimensional obstruction. -/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace DoublingHilbert

namespace ColorBlock
variable {j : ℕ}

end ColorBlock

namespace PeriodGrid
variable {j : ℕ}

end PeriodGrid

section LineSelection
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The independent vertical-line selection, with the same avoidance of FTC null sets. -/
theorem exists_vertical_line (I J : Segment) {F G : Base → E} {C C' : NNReal}
    (hF : LipschitzWith C F) (hG : LipschitzWith C' G)
    {e : Base → ℝ} (he : IsBoundedField e) {c : ℝ} (hc : 0 ≤ c)
    (hdom : ∀ x ∈ Ioo I.lo I.hi, ∀ y : ℝ,
      c * ‖column G (0, 1) (x, y) - column F (0, 1) (x, y)‖ ^ 2 ≤ e (x, y)) :
    ∃ x ∈ Ioo I.lo I.hi, ∀ a ∈ Icc J.lo J.hi, ∀ b ∈ Icc J.lo J.hi,
      c * ‖(G (x, b) - F (x, b)) - (G (x, a) - F (x, a))‖ ^ 2 ≤
        J.length ^ 2 * (∫ p, e p ∂(Rectangle.mk I J).law) := by
  have hgood := I.ae_mem.and
    ((I.ae_of_ae (ae_integral_column_y hG)).and (I.ae_of_ae (ae_integral_column_y hF)))
  obtain ⟨x, ⟨hx, hGx, hFx⟩, hxe⟩ :=
    exists_good_le_integral ((he.integral_snd J.law).integrable I.law) hgood
  refine ⟨x, hx, ?_⟩
  intro a ha b hb
  let g : ℝ → E := fun y => column G (0, 1) (x, y) - column F (0, 1) (x, y)
  have hg : IsBoundedField g :=
    ((boundedField_column hG (0, 1)).sub (boundedField_column hF (0, 1))).comp_measurable
      (measurable_const.prodMk measurable_id)
  have hFTC : ∀ a b, (∫ y in a..b, g y) =
      (G (x, b) - F (x, b)) - (G (x, a) - F (x, a)) := by
    intro a b
    dsimp [g]
    rw [intervalIntegral.integral_sub (intervalIntegrable_column_y hG _ x a b)
      (intervalIntegrable_column_y hF _ x a b), hGx, hFx]
    abel
  have hosc := oscillation_sq_le_segment_energy J hg hFTC ha hb
  have hline : c * (∫ y, ‖g y‖ ^ 2 ∂J.law) ≤ ∫ y, e (x, y) ∂J.law := by
    rw [← integral_const_mul]
    exact integral_mono ((hg.norm_sq.const_mul c).integrable J.law)
      ((he.comp_measurable (measurable_const.prodMk measurable_id)).integrable J.law)
      (fun y => hdom x hx y)
  have hbnd := mul_le_mul_of_nonneg_left hline (sq_nonneg J.length)
  have hbnd' := mul_le_mul_of_nonneg_left hxe (sq_nonneg J.length)
  rw [← (Rectangle.mk I J).integral_eq e (he.integrable _)] at hbnd'
  nlinarith [mul_le_mul_of_nonneg_left hosc hc]

end LineSelection
end DoublingHilbert

namespace DoublingHilbert
section BlockSelection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end BlockSelection
end DoublingHilbert

namespace DoublingHilbert

section CrossingPacking
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end CrossingPacking
end DoublingHilbert

end

end OAI

-- ---- platform node ----
open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Metric
open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem solution (I J : Segment) {F G : Base → E} {C C' : NNReal}
    (hF : LipschitzWith C F) (hG : LipschitzWith C' G)
    {e : Base → ℝ} (he : IsBoundedField e) {c : ℝ} (hc : 0 ≤ c)
    (hdom : ∀ x ∈ Ioo I.lo I.hi, ∀ y : ℝ,
      c * ‖column G (0, 1) (x, y) - column F (0, 1) (x, y)‖ ^ 2 ≤ e (x, y)) :
    ∃ x ∈ Ioo I.lo I.hi, ∀ a ∈ Icc J.lo J.hi, ∀ b ∈ Icc J.lo J.hi,
      c * ‖(G (x, b) - F (x, b)) - (G (x, a) - F (x, a))‖ ^ 2 ≤
        J.length ^ 2 * (∫ p, e p ∂(Rectangle.mk I J).law) := by
  first
    | exact OAI.DoublingHilbert.exists_vertical_line I J hF hG he hc hdom
    | exact OAI.DoublingHilbert.exists_vertical_line
    | (apply OAI.DoublingHilbert.exists_vertical_line <;> assumption)
    | (intros; apply OAI.DoublingHilbert.exists_vertical_line <;> assumption)
