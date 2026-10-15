-- Prove2me | solution 1 for OAI.DoublingHilbert.oscillation_sq_le_segment_energy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:08:04.06232+00:00
-- url     : https://prove2.me/submissions/f52918e6-3bda-4815-ab79-6c44f5beee7c

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Grids.lean:L238-L279
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.oscillation_sq_le_segment_energy. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids

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

/-- Hilbert-space Cauchy--Schwarz in the form needed for line transport;
in fact convexity makes this valid for every normed target. -/
theorem norm_average_sq_le_average_norm_sq [IsFiniteMeasure μ] [NeZero μ]
    {G : X → E} (hG : Integrable G μ)
    (hG2 : Integrable (fun x => ‖G x‖ ^ 2) μ) :
    ‖⨍ x, G x ∂μ‖ ^ 2 ≤ ⨍ x, ‖G x‖ ^ 2 ∂μ := by
  exact ((convexOn_norm (convex_univ : Convex ℝ (Set.univ : Set E))).pow
    (fun _ _ => norm_nonneg _) 2).map_average_le
      (continuous_norm.pow 2).continuousOn isClosed_univ
      (Eventually.of_forall fun _ => mem_univ _) hG hG2

/-- The integral version of the preceding averaged estimate, retaining the exact mass. -/
theorem norm_integral_sq_le_mass_mul [IsFiniteMeasure μ]
    {G : X → E} (hG : Integrable G μ)
    (hG2 : Integrable (fun x => ‖G x‖ ^ 2) μ) :
    ‖∫ x, G x ∂μ‖ ^ 2 ≤ μ.real Set.univ * (∫ x, ‖G x‖ ^ 2 ∂μ) := by
  by_cases hμ : μ = 0
  · subst μ; simp
  have : NeZero μ := ⟨hμ⟩
  have hm := measureReal_univ_pos (μ := μ)
  have hj := norm_average_sq_le_average_norm_sq hG hG2
  simp only [average_eq, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg hm.le, smul_eq_mul, ← div_eq_inv_mul] at hj
  have hj' := mul_le_mul_of_nonneg_left hj (sq_nonneg (μ.real univ))
  field_simp at hj'
  nlinarith

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

theorem norm_sq {g : X → E} (hg : IsBoundedField g) :
    IsBoundedField (fun x => ‖g x‖ ^ 2) := by
  obtain ⟨M, hM⟩ := hg.2
  refine ⟨hg.1.norm.pow 2, M ^ 2, fun x => ?_⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hM x) 2

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

namespace Segment

end Segment

namespace Rectangle

end Rectangle

end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

/-- An FTC identity on all subintervals controls all points of a line, not just a.e. points. -/
theorem oscillation_sq_le_segment_energy {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (I : Segment) {f g : ℝ → E}
    (hg : IsBoundedField g)
    (hFTC : ∀ a b, (∫ x in a..b, g x) = f b - f a)
    {a b : ℝ} (ha : a ∈ Icc I.lo I.hi) (hb : b ∈ Icc I.lo I.hi) :
    ‖f b - f a‖ ^ 2 ≤ I.length ^ 2 * (∫ x, ‖g x‖ ^ 2 ∂I.law) := by
  suffices h : ∀ a b, a ∈ Icc I.lo I.hi → b ∈ Icc I.lo I.hi → a ≤ b →
      ‖f b - f a‖ ^ 2 ≤ I.length ^ 2 * (∫ x, ‖g x‖ ^ 2 ∂I.law) by
    rcases le_total a b with hab | hba
    · exact h a b ha hb hab
    · simpa only [norm_sub_rev] using h b a hb ha hba
  intro a b ha hb hab
  have hgi := I.integrable_iff.mp (hg.integrable I.law)
  have hg2i := I.integrable_iff.mp (hg.norm_sq.integrable I.law)
  have hsub : uIcc a b ⊆ uIcc I.lo I.hi := by
    rw [uIcc_of_le hab, uIcc_of_le I.lt.le]
    exact Icc_subset_Icc ha.1 hb.2
  have hgab := hgi.mono_set hsub
  have hg2ab := hg2i.mono_set hsub
  have hcs := norm_integral_sq_le_mass_mul hgab.1 hg2ab.1
  have hcs' : ‖f b - f a‖ ^ 2 ≤ (b - a) * (∫ x in a..b, ‖g x‖ ^ 2) := by
    rw [← hFTC a b, intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_of_le hab]
    simpa only [measureReal_restrict_apply_univ, Real.volume_real_Ioc,
      max_eq_left (sub_nonneg.mpr hab)] using hcs
  have hmono : (∫ x in a..b, ‖g x‖ ^ 2) ≤
      (∫ x in I.lo..I.hi, ‖g x‖ ^ 2) := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le I.lt.le]
    exact setIntegral_mono_set hg2i.1 (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall fun _ hx => ⟨ha.1.trans_lt hx.1, hx.2.trans hb.2⟩)
  have hnonneg : 0 ≤ (∫ x in I.lo..I.hi, ‖g x‖ ^ 2) :=
    intervalIntegral.integral_nonneg I.lt.le (fun _ _ => sq_nonneg _)
  have hlen : b - a ≤ I.length := by dsimp [Segment.length]; linarith [ha.1, hb.2]
  calc
    _ ≤ (b - a) * (∫ x in a..b, ‖g x‖ ^ 2) := hcs'
    _ ≤ I.length * (∫ x in I.lo..I.hi, ‖g x‖ ^ 2) :=
      (mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hab)).trans
        (mul_le_mul_of_nonneg_right hlen hnonneg)
    _ = _ := by
      rw [I.integral_eq, smul_eq_mul]
      field_simp

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
open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (I : Segment) {f g : ℝ → E}
    (hg : IsBoundedField g)
    (hFTC : ∀ a b, (∫ x in a..b, g x) = f b - f a)
    {a b : ℝ} (ha : a ∈ Icc I.lo I.hi) (hb : b ∈ Icc I.lo I.hi) :
    ‖f b - f a‖ ^ 2 ≤ I.length ^ 2 * (∫ x, ‖g x‖ ^ 2 ∂I.law) := by
  first
    | exact OAI.DoublingHilbert.oscillation_sq_le_segment_energy I hg hFTC ha hb
    | exact OAI.DoublingHilbert.oscillation_sq_le_segment_energy
    | (apply OAI.DoublingHilbert.oscillation_sq_le_segment_energy <;> assumption)
    | (intros; apply OAI.DoublingHilbert.oscillation_sq_le_segment_energy <;> assumption)
