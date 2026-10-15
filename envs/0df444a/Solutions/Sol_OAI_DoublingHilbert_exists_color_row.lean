-- Prove2me | solution 1 for OAI.DoublingHilbert.exists_color_row
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:39:47.867706+00:00
-- url     : https://prove2.me/submissions/8e0a131b-3b59-4d5f-81c1-5d611ee77720

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Crossings.lean:L206-L233
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.exists_color_row. The node keeps its source
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
import Theorems.Thm_OAI_DoublingHilbert_IsBoundedField_select
import Theorems.Thm_OAI_DoublingHilbert_Segment_integral_grid
import Theorems.Thm_OAI_DoublingHilbert_exists_horizontal_line

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

omit [CompleteSpace E] in
theorem globalSheet_lipschitz {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) :
    ∃ L : NNReal, LipschitzWith L (globalSheet hf w) := by
  obtain ⟨L, hL, _⟩ :=
    (exists_lipschitz_extension_finiteDimensional (embeddingSheet_lipschitz hf w)).choose_spec
  exact ⟨L, hL⟩

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

variable [NormedSpace ℝ E]

theorem integral_fst {g : X × Y → E} (hg : IsBoundedField g) (μ : Measure X)
    [IsProbabilityMeasure μ] : IsBoundedField (fun y => ∫ x, g (x, y) ∂μ) := by
  obtain ⟨M, hM⟩ := hg.2
  refine ⟨hg.1.integral_prod_left', M, fun y => ?_⟩
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall fun x => hM (x, y))

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

/-- Exact integration by rows. -/
theorem integral_grid_y {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a h : ℝ) {n : ℕ} (hh : 0 < h) (hn : 0 < n) (I : Segment) {g : ℝ × ℝ → E}
    (hg : IsBoundedField g) :
    (∫ p, g p ∂(Rectangle.mk I (Segment.grid a h n hh hn)).law) =
      (n : ℝ)⁻¹ • ∑ i : Fin n, ∫ p, g p ∂(Rectangle.mk I (Segment.cell a h hh i)).law := by
  rw [(Rectangle.mk I (Segment.grid a h n hh hn)).integral_eq_swap g
    (hg.integrable _), Segment.integral_grid a h hh hn (hg.integral_fst I.law)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact ((Rectangle.mk I (Segment.cell a h hh i)).integral_eq_swap g
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

theorem measurable_stripColor (N : ℕ) (hN : 0 < N) (h : ℝ) :
    Measurable (stripColor N hN h) := by
  let c : ℤ → Fin N := fun z => ⟨(z % (N : ℤ)).toNat, by
    have hnonneg := Int.emod_nonneg z (by exact_mod_cast hN.ne' : (N : ℤ) ≠ 0)
    have hlt := Int.emod_lt_of_pos z (by exact_mod_cast hN : (0 : ℤ) < N)
    exact_mod_cast (Int.toNat_lt hnonneg).mpr hlt⟩
  exact (measurable_of_countable c).comp
    (Int.measurable_floor.comp (measurable_id.div_const h))

theorem floor_div_of_mem_strip {h t : ℝ} (hh : 0 < h) (q : ℤ)
    (ht : t ∈ Ioo ((q : ℝ) * h) (((q : ℝ) + 1) * h)) : ⌊t / h⌋ = q := by
  apply Int.floor_eq_iff.mpr
  exact ⟨(le_div_iff₀ hh).mpr ht.1.le, (div_lt_iff₀ hh).mpr ht.2⟩

theorem stripColor_eq_of_mem_strip (N : ℕ) (hN : 0 < N) {h t : ℝ} (hh : 0 < h)
    (q : ℤ) (i : Fin N) (hq : q % (N : ℤ) = (i : ℕ))
    (ht : t ∈ Ioo ((q : ℝ) * h) (((q : ℝ) + 1) * h)) :
    stripColor N hN h t = i := by
  apply Fin.ext
  simp only [stripColor, floor_div_of_mem_strip hh q ht, hq, Int.toNat_natCast]

/-- Each color appears exactly once in a complete period block. -/
theorem color_in_block (N : ℕ) (hN : 0 < N) {h t : ℝ} (hh : 0 < h)
    (b : ℤ) (i : Fin N)
    (ht : t ∈ Ioo (((b : ℝ) * N + i) * h) (((b : ℝ) * N + i + 1) * h)) :
    stripColor N hN h t = i ∧ inColoredStrip h N i t := by
  let q : ℤ := b * (N : ℤ) + (i : ℕ)
  have hq : q % (N : ℤ) = (i : ℕ) := by
    dsimp [q]
    rw [Int.add_emod, Int.mul_emod_left, zero_add, Int.emod_emod]
    exact Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le (i : ℕ)) (by exact_mod_cast i.isLt)
  have hqcast : (q : ℝ) = (b : ℝ) * N + i := by simp [q]
  have ht' : t ∈ Ioo ((q : ℝ) * h) (((q : ℝ) + 1) * h) := by rwa [hqcast]
  exact ⟨stripColor_eq_of_mem_strip N hN hh q i hq ht', q, hq, ht'.1, ht'.2⟩

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

theorem integral_row_le_mul_grid (a h : ℝ) {n : ℕ} (hh : 0 < h) (hn : 0 < n)
    (I : Segment) {g : ℝ × ℝ → ℝ} (hg : IsBoundedField g) (hpos : ∀ p, 0 ≤ g p)
    (i : Fin n) :
    (∫ p, g p ∂(Rectangle.mk I (Segment.cell a h hh i)).law) ≤
      n * (∫ p, g p ∂(Rectangle.mk I (Segment.grid a h n hh hn)).law) := by
  rw [integral_grid_y a h hh hn I hg, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0), one_mul]
  exact Finset.single_le_sum (f := fun j : Fin n => ∫ p, g p ∂(Rectangle.mk I (Segment.cell a h hh j)).law)
    (fun j _ => integral_nonneg hpos) (Finset.mem_univ i)

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

theorem add {f g : X → E} (hf : IsBoundedField f) (hg : IsBoundedField g) :
    IsBoundedField (fun x => f x + g x) := by
  obtain ⟨M, hM⟩ := hf.2
  obtain ⟨N, hN⟩ := hg.2
  exact ⟨hf.1.add hg.1, M + N,
    fun x => (norm_add_le _ _).trans (add_le_add (hM x) (hN x))⟩

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

omit [CompleteSpace E] in
theorem bounded_horizontalColumn {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (v : Base) :
    IsBoundedField (horizontalColumn hf w j v) := by
  unfold horizontalColumn
  apply IsBoundedField.select (g := fun i p => column (addedSheet hf w j i) v p)
    _ ((measurable_stripColor (colors j) (colors_pos j) (scale j)).comp measurable_snd)
  intro i
  obtain ⟨C, hC⟩ := globalSheet_lipschitz hf (w.update j ((i : ℕ) + 1))
  exact boundedField_column hC v

omit [CompleteSpace E] in
theorem bounded_verticalColumn {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (v : Base) :
    IsBoundedField (verticalColumn hf w j v) := by
  unfold verticalColumn
  apply IsBoundedField.select (g := fun i p => column (addedSheet hf w j i) v p)
    _ ((measurable_stripColor (colors j) (colors_pos j) (stripWidth j)).comp measurable_fst)
  intro i
  obtain ⟨C, hC⟩ := globalSheet_lipschitz hf (w.update j ((i : ℕ) + 1))
  exact boundedField_column hC v

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

-- ---- from OAI.Geometry.DoublingHilbert.Energy ----
namespace OAI

/-! Anisotropic energy bounds and arbitrarily small-energy period grids. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

section ProbabilityEnergy
variable {X E : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end ProbabilityEnergy

section Energies
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
theorem bounded_baseColumn {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (v : Base) :
    IsBoundedField (column (globalSheet hf w) v) := by
  obtain ⟨C, hC⟩ := globalSheet_lipschitz hf w
  exact boundedField_column hC v

omit [CompleteSpace E] in
theorem bounded_horizontalEnergy {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) :
    IsBoundedField (horizontalEnergy hf w j) :=
  ((bounded_horizontalColumn hf w j _).sub (bounded_baseColumn hf w _)).norm_sq

omit [CompleteSpace E] in
theorem bounded_verticalEnergy {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) :
    IsBoundedField (verticalEnergy hf w j) :=
  ((bounded_verticalColumn hf w j _).sub (bounded_baseColumn hf w _)).norm_sq

omit [CompleteSpace E] in
theorem bounded_combinedEnergy {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) :
    IsBoundedField (combinedEnergy hf w j) :=
  ((bounded_horizontalEnergy hf w j).const_mul _).add (bounded_verticalEnergy hf w j)

omit [CompleteSpace E] in
theorem combinedEnergy_nonneg {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (p : Base) :
    0 ≤ combinedEnergy hf w j p := by
  unfold combinedEnergy horizontalEnergy verticalEnergy
  positivity

end Energies

end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

section AnisotropicEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end AnisotropicEnergy
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section
section NearMaxGrid
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end NearMaxGrid
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

section SmallEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end SmallEnergy
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

theorem row_color (B : ColorBlock j) (i : Fin (colors j)) {y : ℝ}
    (hy : y ∈ Ioo (B.row i).lo (B.row i).hi) :
    stripColor (colors j) (colors_pos j) (scale j) y = i ∧
      inColoredStrip (scale j) (colors j) i y := by
  apply color_in_block _ _ (scale_pos j) B.ay i
  simp only [row, Segment.cell, Nat.cast_add, Nat.cast_one, mem_Ioo] at hy
  dsimp [yPeriod] at hy
  constructor <;> nlinarith [hy.1, hy.2]

theorem row_energy_le (B : ColorBlock j) (i : Fin (colors j))
    {g : Base → ℝ} (hg : IsBoundedField g) (hnonneg : ∀ p, 0 ≤ g p) :
    (∫ p, g p ∂(Rectangle.mk B.rectangle.x (B.row i)).law) ≤
      colors j * (∫ p, g p ∂B.rectangle.law) :=
  Rectangle.integral_row_le_mul_grid _ _ (scale_pos j) (colors_pos j) _ hg hnonneg i

end ColorBlock

namespace PeriodGrid
variable {j : ℕ}

end PeriodGrid

section LineSelection
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end LineSelection
end DoublingHilbert

namespace DoublingHilbert
section BlockSelection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Every color has a selected horizontal line; the anisotropic weight is retained. -/
theorem exists_color_row {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (B : ColorBlock j)
    (i : Fin (colors j)) :
    ∃ y ∈ Ioo (B.row i).lo (B.row i).hi,
      ∀ a ∈ Icc B.rectangle.x.lo B.rectangle.x.hi,
      ∀ b ∈ Icc B.rectangle.x.lo B.rectangle.x.hi,
      (widthFactor j : ℝ) ^ 2 *
        ‖(addedSheet hf w j i (b, y) - globalSheet hf w (b, y)) -
          (addedSheet hf w j i (a, y) - globalSheet hf w (a, y))‖ ^ 2 ≤
        B.rectangle.x.length ^ 2 *
          (colors j * (∫ p, combinedEnergy hf w j p ∂B.rectangle.law)) := by
  obtain ⟨C, hF⟩ := globalSheet_lipschitz hf w
  obtain ⟨C', hG⟩ := globalSheet_lipschitz hf (w.update j ((i : ℕ) + 1))
  have hdom : ∀ y ∈ Ioo (B.row i).lo (B.row i).hi, ∀ x : ℝ,
      (widthFactor j : ℝ) ^ 2 *
        ‖column (addedSheet hf w j i) (1, 0) (x, y) -
          column (globalSheet hf w) (1, 0) (x, y)‖ ^ 2 ≤ combinedEnergy hf w j (x, y) := by
    intro y hy x
    unfold combinedEnergy horizontalEnergy horizontalColumn
    rw [(B.row_color i hy).1]
    exact le_add_of_nonneg_right (sq_nonneg _)
  obtain ⟨y, hy, hosc⟩ := exists_horizontal_line B.rectangle.x (B.row i) hF hG
    (bounded_combinedEnergy hf w j) (sq_nonneg (widthFactor j : ℝ)) hdom
  refine ⟨y, hy, fun a ha b hb => (hosc a ha b hb).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (B.row_energy_le i (bounded_combinedEnergy hf w j) (combinedEnergy_nonneg hf w j))
    (sq_nonneg _)

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem solution {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (B : ColorBlock j)
    (i : Fin (colors j)) :
    ∃ y ∈ Ioo (B.row i).lo (B.row i).hi,
      ∀ a ∈ Icc B.rectangle.x.lo B.rectangle.x.hi,
      ∀ b ∈ Icc B.rectangle.x.lo B.rectangle.x.hi,
      (widthFactor j : ℝ) ^ 2 *
        ‖(addedSheet hf w j i (b, y) - globalSheet hf w (b, y)) -
          (addedSheet hf w j i (a, y) - globalSheet hf w (a, y))‖ ^ 2 ≤
        B.rectangle.x.length ^ 2 *
          (colors j * (∫ p, combinedEnergy hf w j p ∂B.rectangle.law)) := by
  first
    | exact OAI.DoublingHilbert.exists_color_row hf w j B i
    | exact OAI.DoublingHilbert.exists_color_row
    | (apply OAI.DoublingHilbert.exists_color_row <;> assumption)
    | (intros; apply OAI.DoublingHilbert.exists_color_row <;> assumption)
