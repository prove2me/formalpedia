-- Prove2me | solution 1 for OAI.DoublingHilbert.horizontal_mean_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:59:46.829212+00:00
-- url     : https://prove2.me/submissions/c9818e47-5dd9-42c2-a37c-d5434f4e6d3f

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Rectangles.lean:L235-L269
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.horizontal_mean_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Theorems.Thm_OAI_DoublingHilbert_IsBoundedField_select

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
theorem intervalIntegrable_column_x {f : ℝ × ℝ → E} {C : NNReal} (hf : LipschitzWith C f)
    (v : ℝ × ℝ) (y a b : ℝ) :
    IntervalIntegrable (fun x => column f v (x, y)) volume a b := by
  apply intervalIntegrable_of_bound
    ((stronglyMeasurable_column f v).comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  intro x
  exact norm_column_le hf v (x, y)

omit [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem lipschitz_line_x {f : ℝ × ℝ → E} {C : NNReal} (hf : LipschitzWith C f) (y : ℝ) :
    LipschitzWith C (fun x => f (x, y)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x x'
  simpa only [dist_prod_same_right] using hf.dist_le_mul (x, y) (x', y)

omit [CompleteSpace E] in
theorem ae_line_derivative_x {f : ℝ × ℝ → E} {C : NNReal} (hf : LipschitzWith C f) :
    ∀ᵐ y, ∀ᵐ x, HasDerivAt (fun t => f (t, y)) (column f (1, 0) (x, y)) x := by
  have hd := hf.ae_differentiableAt (μ := (volume : Measure (ℝ × ℝ)))
  rw [Measure.volume_eq_prod] at hd
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hd
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with y hy
  filter_upwards [hy] with x hx
  exact hx.hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))

/-- Fubini plus the vector FTC controls every subinterval on almost every horizontal line. -/
theorem ae_integral_column_x {f : ℝ × ℝ → E} {C : NNReal} (hf : LipschitzWith C f) :
    ∀ᵐ y, ∀ a b : ℝ, (∫ x in a..b, column f (1, 0) (x, y)) = f (b, y) - f (a, y) := by
  filter_upwards [ae_line_derivative_x hf] with y hy
  intro a b
  exact integral_eq_sub_of_lipschitz_ae_derivative (lipschitz_line_x hf y).lipschitzOnWith
    (intervalIntegrable_column_x hf (1, 0) y a b) (hy.mono fun _ h _ => h)

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

theorem ae_of_ae (I : Segment) {P : ℝ → Prop} (hP : ∀ᵐ x, P x) :
    ∀ᵐ x ∂I.law, P x := I.ae_iff.mpr (hP.mono fun _ hx _ => hx)

theorem integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Segment) (g : ℝ → E) :
    (∫ x, g x ∂I.law) = I.length⁻¹ • ∫ x in I.lo..I.hi, g x := by
  rw [law, integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofReal I.length_pos.le,
    intervalIntegral.integral_of_le I.lt.le]

end Segment

namespace Rectangle

theorem integral_eq_swap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Rectangle) (g : ℝ × ℝ → E) (hg : Integrable g Q.law) :
    (∫ p, g p ∂Q.law) = ∫ y, ∫ x, g (x, y) ∂Q.x.law ∂Q.y.law :=
  (integral_prod g hg).trans (integral_integral_swap hg)

end Rectangle

section BoundedFields
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

namespace IsBoundedField

theorem integrable {g : X → E} (hg : IsBoundedField g) (μ : Measure X)
    [IsFiniteMeasure μ] : Integrable g μ := by
  obtain ⟨M, hM⟩ := hg.2
  exact Integrable.of_bound hg.1.aestronglyMeasurable M (Eventually.of_forall hM)

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

omit [CompleteSpace E] in
theorem boundedField_column {f : Base → E} {C : NNReal} (hf : LipschitzWith C f)
    (v : Base) : IsBoundedField (column f v) :=
  ⟨stronglyMeasurable_column f v, C * ‖v‖, norm_column_le hf v⟩

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem norm_integral_rectangle_le_x (Q : Rectangle) {G : Base → E}
    (hG : IsBoundedField G) {R : ℝ}
    (hline : ∀ᵐ y ∂Q.y.law, ‖∫ x, G (x, y) ∂Q.x.law‖ ≤ R) :
    ‖∫ p, G p ∂Q.law‖ ≤ R := by
  rw [Q.integral_eq_swap G (hG.integrable Q.law)]
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hline

/-- Endpoint transport for a measurably selected horizontal sheet on each row. -/
theorem horizontal_mean_bound {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (Q : Rectangle)
    {F : Base → E} {G : ι → Base → E} {C : NNReal} {C' : ι → NNReal}
    (hF : LipschitzWith C F) (hG : ∀ i, LipschitzWith (C' i) (G i))
    {σ : ℝ → ι} (hσ : Measurable σ) {R : ℝ}
    (hleft : ∀ᵐ y ∂Q.y.law, ‖G (σ y) (Q.x.lo, y) - F (Q.x.lo, y)‖ ≤ R)
    (hright : ∀ᵐ y ∂Q.y.law, ‖G (σ y) (Q.x.hi, y) - F (Q.x.hi, y)‖ ≤ R) :
    ‖(∫ p, column (G (σ p.2)) (1, 0) p ∂Q.law) -
      (∫ p, column F (1, 0) p ∂Q.law)‖ ≤ 2 * R / Q.x.length := by
  have hB : IsBoundedField (fun p => column (G (σ p.2)) (1, 0) p) :=
    IsBoundedField.select (fun i => boundedField_column (hG i) (1, 0))
    (hσ.comp measurable_snd)
  have hBF := boundedField_column hF (1, 0)
  rw [← integral_sub (hB.integrable Q.law) (hBF.integrable Q.law)]
  apply norm_integral_rectangle_le_x Q (hB.sub hBF)
  have hlines : ∀ᵐ y, ∀ i, ∀ a b : ℝ,
      (∫ x in a..b, column (G i) (1, 0) (x, y)) = G i (b, y) - G i (a, y) :=
    ae_all_iff.mpr fun i => ae_integral_column_x (hG i)
  filter_upwards [Q.y.ae_of_ae hlines, Q.y.ae_of_ae (ae_integral_column_x hF), hleft, hright]
    with y hy hFy hly hry
  rw [Q.x.integral_eq, intervalIntegral.integral_sub
    (intervalIntegrable_column_x (hG (σ y)) (1, 0) y _ _)
    (intervalIntegrable_column_x hF (1, 0) y _ _), hy, hFy]
  have heq : G (σ y) (Q.x.hi, y) - G (σ y) (Q.x.lo, y) -
      (F (Q.x.hi, y) - F (Q.x.lo, y)) =
      (G (σ y) (Q.x.hi, y) - F (Q.x.hi, y)) -
      (G (σ y) (Q.x.lo, y) - F (Q.x.lo, y)) := by abel
  rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos Q.x.length_pos]
  have hh := (norm_sub_le (G (σ y) (Q.x.hi, y) - F (Q.x.hi, y))
    (G (σ y) (Q.x.lo, y) - F (Q.x.lo, y))).trans
      (add_le_add hry hly)
  calc
    _ ≤ Q.x.length⁻¹ * (R + R) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr Q.x.length_pos.le)
    _ = _ := by ring

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
open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem solution {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (Q : Rectangle)
    {F : Base → E} {G : ι → Base → E} {C : NNReal} {C' : ι → NNReal}
    (hF : LipschitzWith C F) (hG : ∀ i, LipschitzWith (C' i) (G i))
    {σ : ℝ → ι} (hσ : Measurable σ) {R : ℝ}
    (hleft : ∀ᵐ y ∂Q.y.law, ‖G (σ y) (Q.x.lo, y) - F (Q.x.lo, y)‖ ≤ R)
    (hright : ∀ᵐ y ∂Q.y.law, ‖G (σ y) (Q.x.hi, y) - F (Q.x.hi, y)‖ ≤ R) :
    ‖(∫ p, column (G (σ p.2)) (1, 0) p ∂Q.law) -
      (∫ p, column F (1, 0) p ∂Q.law)‖ ≤ 2 * R / Q.x.length := by
  first
    | exact OAI.DoublingHilbert.horizontal_mean_bound Q hF hG hσ hleft hright
    | exact OAI.DoublingHilbert.horizontal_mean_bound
    | (apply OAI.DoublingHilbert.horizontal_mean_bound <;> assumption)
    | (intros; apply OAI.DoublingHilbert.horizontal_mean_bound <;> assumption)
