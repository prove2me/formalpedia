-- Prove2me | solution 1 for OAI.DoublingHilbert.horizontal_mean_bound_stripes
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:11:17.526847+00:00
-- url     : https://prove2.me/submissions/cb221926-f69a-41b3-a05a-533e46485907

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/SelectedSheets.lean:L38-L93
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.horizontal_mean_bound_stripes. The node keeps its source
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
import Theorems.Thm_OAI_DoublingHilbert_IsBoundedField_select
import Theorems.Thm_OAI_DoublingHilbert_Segment_integral_grid
import Theorems.Thm_OAI_DoublingHilbert_horizontal_mean_bound

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

end Segment

namespace Rectangle

theorem ae_mem (Q : Rectangle) : ∀ᵐ p ∂Q.law, p ∈ Q.interior := by
  exact ((Measure.quasiMeasurePreserving_fst.ae Q.x.ae_mem).and
    (Measure.quasiMeasurePreserving_snd.ae Q.y.ae_mem))

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

/-- Exact integration by columns. -/
theorem integral_grid_x {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a h : ℝ) {n : ℕ} (hh : 0 < h) (hn : 0 < n) (J : Segment) {g : ℝ × ℝ → E}
    (hg : IsBoundedField g) :
    (∫ p, g p ∂(Rectangle.mk (Segment.grid a h n hh hn) J).law) =
      (n : ℝ)⁻¹ • ∑ i : Fin n, ∫ p, g p ∂(Rectangle.mk (Segment.cell a h hh i) J).law := by
  rw [(Rectangle.mk (Segment.grid a h n hh hn) J).integral_eq g
    (hg.integrable _), Segment.integral_grid a h hh hn (hg.integral_snd J.law)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact ((Rectangle.mk (Segment.cell a h hh i) J).integral_eq g
    (hg.integrable _)).symm

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

/-- Endpoint bounds on an open real interval extend to its endpoints by continuity. -/
theorem norm_le_on_Icc_of_Ioo {E : Type*} [NormedAddCommGroup E]
    {g : ℝ → E} (hg : Continuous g) {a b R : ℝ} (hab : a < b)
    (hbound : ∀ x ∈ Ioo a b, ‖g x‖ ≤ R) : ∀ x ∈ Icc a b, ‖g x‖ ≤ R := by
  have hsub : Ioo a b ⊆ {x | ‖g x‖ ≤ R} := hbound
  have hcl := closure_minimal hsub (isClosed_le hg.norm continuous_const)
  rw [closure_Ioo hab.ne] at hcl
  exact hcl

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

end IsBoundedField

section StripeMeans
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/-- Horizontal integration on each separate vertical strip; discontinuous selections
are never differentiated across strip boundaries. -/
theorem horizontal_mean_bound_stripes {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (a h : ℝ) {n : ℕ} (hh : 0 < h) (hn : 0 < n)
    (J : Segment) {F : Base → E} {G : ι → Base → E}
    {C : NNReal} {C' : ι → NNReal}
    (hF : LipschitzWith C F) (hG : ∀ i, LipschitzWith (C' i) (G i))
    {σ : ℝ → ι} (hσ : Measurable σ) (c : Fin n → ι) {R : ℝ}
    (hcolor : ∀ i : Fin n, ∀ x ∈ Ioo (Segment.cell a h hh i).lo
      (Segment.cell a h hh i).hi, σ x = c i)
    (hbound : ∀ i : Fin n, ∀ x ∈ Ioo (Segment.cell a h hh i).lo
      (Segment.cell a h hh i).hi, ∀ y ∈ Ioo J.lo J.hi, ‖G (c i) (x, y) - F (x, y)‖ ≤ R) :
    ‖(∫ p, column (G (σ p.1)) (1, 0) p ∂(Rectangle.mk (Segment.grid a h n hh hn) J).law) -
      (∫ p, column F (1, 0) p ∂(Rectangle.mk (Segment.grid a h n hh hn) J).law)‖ ≤
      2 * R / h := by
  let Q : Rectangle := ⟨Segment.grid a h n hh hn, J⟩
  let Qi (i : Fin n) : Rectangle := ⟨Segment.cell a h hh i, J⟩
  have hB : IsBoundedField (fun p => column (G (σ p.1)) (1, 0) p) :=
    IsBoundedField.select (fun i => boundedField_column (hG i) (1, 0))
      (hσ.comp measurable_fst)
  have hBF := boundedField_column hF (1, 0)
  have hcell : ∀ i : Fin n,
      ‖∫ p, column (G (σ p.1)) (1, 0) p - column F (1, 0) p ∂(Qi i).law‖ ≤ 2 * R / h := by
    intro i
    have hend : ∀ y ∈ Ioo J.lo J.hi, ∀ x ∈ Icc (Qi i).x.lo (Qi i).x.hi,
        ‖G (c i) (x, y) - F (x, y)‖ ≤ R := by
      intro y hy
      apply norm_le_on_Icc_of_Ioo
        (((hG (c i)).continuous.comp (continuous_id.prodMk continuous_const)).sub
          (hF.continuous.comp (continuous_id.prodMk continuous_const))) (Qi i).x.lt
      exact fun x hx => hbound i x hx y hy
    have he := horizontal_mean_bound (Qi i) hF hG (σ := fun _ => c i) measurable_const
      (J.ae_mem.mono fun y hy => hend y hy _ ⟨le_rfl, (Qi i).x.lt.le⟩)
      (J.ae_mem.mono fun y hy => hend y hy _ ⟨(Qi i).x.lt.le, le_rfl⟩)
    have hBC := boundedField_column (hG (c i)) (1, 0)
    rw [← integral_sub (hBC.integrable _) (hBF.integrable _)] at he
    have heq : (∫ p, column (G (σ p.1)) (1, 0) p - column F (1, 0) p ∂(Qi i).law) =
        ∫ p, column (G (c i)) (1, 0) p - column F (1, 0) p ∂(Qi i).law := by
      apply integral_congr_ae
      filter_upwards [(Qi i).ae_mem] with p hp
      rw [hcolor i p.1 hp.1]
    rw [heq]
    simpa only [Qi, Segment.cell_length] using he
  rw [← integral_sub (hB.integrable _) (hBF.integrable _),
    Rectangle.integral_grid_x a h hh hn J (hB.sub hBF)]
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by exact_mod_cast hn : (0 : ℝ) < n)]
  calc
    _ ≤ (n : ℝ)⁻¹ * ∑ i : Fin n,
        ‖∫ p, column (G (σ p.1)) (1, 0) p - column F (1, 0) p ∂(Qi i).law‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, (2 * R / h) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun i _ => hcell i
    _ = 2 * R / h := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0), one_mul]

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

-- ---- platform node ----
open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem solution {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (a h : ℝ) {n : ℕ} (hh : 0 < h) (hn : 0 < n)
    (J : Segment) {F : Base → E} {G : ι → Base → E}
    {C : NNReal} {C' : ι → NNReal}
    (hF : LipschitzWith C F) (hG : ∀ i, LipschitzWith (C' i) (G i))
    {σ : ℝ → ι} (hσ : Measurable σ) (c : Fin n → ι) {R : ℝ}
    (hcolor : ∀ i : Fin n, ∀ x ∈ Ioo (Segment.cell a h hh i).lo
      (Segment.cell a h hh i).hi, σ x = c i)
    (hbound : ∀ i : Fin n, ∀ x ∈ Ioo (Segment.cell a h hh i).lo
      (Segment.cell a h hh i).hi, ∀ y ∈ Ioo J.lo J.hi, ‖G (c i) (x, y) - F (x, y)‖ ≤ R) :
    ‖(∫ p, column (G (σ p.1)) (1, 0) p ∂(Rectangle.mk (Segment.grid a h n hh hn) J).law) -
      (∫ p, column F (1, 0) p ∂(Rectangle.mk (Segment.grid a h n hh hn) J).law)‖ ≤
      2 * R / h := by
  first
    | exact OAI.DoublingHilbert.horizontal_mean_bound_stripes a h hh hn J hF hG hσ c hcolor hbound
    | exact OAI.DoublingHilbert.horizontal_mean_bound_stripes
    | (apply OAI.DoublingHilbert.horizontal_mean_bound_stripes <;> assumption)
    | (intros; apply OAI.DoublingHilbert.horizontal_mean_bound_stripes <;> assumption)
