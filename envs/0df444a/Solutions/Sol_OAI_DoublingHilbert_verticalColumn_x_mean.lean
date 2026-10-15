-- Prove2me | solution 1 for OAI.DoublingHilbert.verticalColumn_x_mean
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:19:54.870159+00:00
-- url     : https://prove2.me/submissions/7831b243-4c80-4789-94d4-7a71a70eb3ad

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/SelectedSheets.lean:L351-L399
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.verticalColumn_x_mean. The node keeps its source
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
import Theorems.Thm_OAI_DoublingHilbert_admissible_update_iff
import Theorems.Thm_OAI_DoublingHilbert_horizontal_mean_bound_stripes

-- ---- from OAI.Geometry.DoublingHilbert.Construction ----
namespace OAI

/-! Recurrent scales and orthogonal displacement sheets in real Hilbert space. -/

open scoped BigOperators
open Set

noncomputable section

namespace DoublingHilbert

theorem tupleVector_update (w : Tuple) (j i : ℕ) (hj : w j = 0) :
    tupleVector (w.update j (i + 1)) = tupleVector w + levelVector j i := by
  classical
  have hjs : j ∉ w.support := by simpa using hj
  rw [tupleVector, Finsupp.support_update_ne_zero w (a := j) (by omega : i + 1 ≠ 0), Finset.sum_insert hjs]
  simp only [Finsupp.update_apply, ite_true, Nat.add_sub_cancel]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  have hmj : m ≠ j := by intro h; subst m; exact hjs hm
  simp [hmj]

theorem point_update (p : Base) (w : Tuple) (j i : ℕ) (hj : w j = 0) :
    point p (w.update j (i + 1)) = point p w + levelVector j i := by
  rw [point, tupleVector_update w j i hj, point, add_assoc]

end DoublingHilbert

end

end OAI

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
theorem globalSheet_lipschitz {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) :
    ∃ L : NNReal, LipschitzWith L (globalSheet hf w) := by
  obtain ⟨L, hL, _⟩ :=
    (exists_lipschitz_extension_finiteDimensional (embeddingSheet_lipschitz hf w)).choose_spec
  exact ⟨L, hL⟩

omit [CompleteSpace E] in
theorem globalSheet_eqOn {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) :
    EqOn (globalSheet hf w) (embeddingSheet f w) (sheetDomain w) := by
  obtain ⟨_, _, heq⟩ :=
    (exists_lipschitz_extension_finiteDimensional (embeddingSheet_lipschitz hf w)).choose_spec
  exact heq.symm

end Extensions
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

namespace Segment

/-- Each component cell lies in its whole grid interval. -/
theorem cell_subset_grid (a h : ℝ) {n : ℕ} (hh : 0 < h) (hn : 0 < n)
    (i : Fin n) :
    Icc (cell a h hh i).lo (cell a h hh i).hi ⊆
      Icc (grid a h n hh hn).lo (grid a h n hh hn).hi := by
  intro t ht
  have hi : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  have hzero : (0 : ℝ) ≤ i := by positivity
  simp only [cell, grid, Nat.cast_add, Nat.cast_one] at ht ⊢
  rcases ht with ⟨htl, htr⟩
  constructor <;> nlinarith

end Segment

end
end DoublingHilbert

namespace DoublingHilbert
open Set Filter MeasureTheory
open scoped Topology
noncomputable section

namespace Segment

theorem grid_subdivision (a h : ℝ) (n N : ℕ) (hh : 0 < h) (hn : 0 < n) (hN : 0 < N) :
    grid a (N * h) n (mul_pos (by exact_mod_cast hN) hh) hn =
      grid a h (n * N) hh (Nat.mul_pos hn hN) := by
  apply ext
  · rfl
  simp only [grid, Nat.cast_mul]
  ring

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

/-- The new sheet's displacement from the base sheet is at most D r wherever it is permitted. -/
theorem globalSheet_offset {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (hj : w j = 0) {i : ℕ}
    (hi : i < colors j) {p : Base} (hp : p ∈ sheetDomain w) (hip : allowed j i p) :
    ‖globalSheet hf (w.update j (i + 1)) p - globalSheet hf w p‖ ≤ D * scale j := by
  have hup := (admissible_update_iff p w j i hj).mpr ⟨hp, hi, hip⟩
  rw [globalSheet_eqOn hf _ hup, globalSheet_eqOn hf _ hp,
    embeddingSheet_eq f _ p hup, embeddingSheet_eq f _ p hp, ← dist_eq_norm]
  have hs : dist (⟨point p (w.update j (i + 1)), point_mem _ _ hup⟩ : constructedSet)
      ⟨point p w, point_mem _ _ hp⟩ = scale j := by
    change dist (point p (w.update j (i + 1))) (point p w) = scale j
    rw [point_update p w j i hj, dist_eq_norm, add_sub_cancel_left, norm_levelVector]
  exact (hf.dist_le_mul _ _).trans_eq (by rw [hs])

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

theorem rectangle_x_subdivided (G : PeriodGrid j) : G.rectangle.x =
    Segment.grid (G.ax * xPeriod j) (stripWidth j) (G.nx * colors j)
      (stripWidth_pos j) (Nat.mul_pos G.nx_pos (colors_pos j)) :=
  Segment.grid_subdivision _ _ _ _ (stripWidth_pos j) G.nx_pos (colors_pos j)

end PeriodGrid

theorem residueColor_val (N : ℕ) (hN : 0 < N) (q : ℤ) :
    ((residueColor N hN q : Fin N) : ℤ) = q % (N : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg q (by exact_mod_cast hN.ne'))

theorem color_on_cell (N : ℕ) (hN : 0 < N) {h : ℝ} (hh : 0 < h)
    (a : ℤ) (i : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (Segment.cell (a * h) h hh i).lo (Segment.cell (a * h) h hh i).hi) :
    stripColor N hN h t = residueColor N hN (a + i) ∧
      inColoredStrip h N (residueColor N hN (a + i)) t := by
  have ht' : t ∈ Ioo (((a + (i : ℤ) : ℤ) : ℝ) * h)
      ((((a + (i : ℤ) : ℤ) : ℝ) + 1) * h) := by
    simp only [Segment.cell, Nat.cast_add, Nat.cast_one] at ht
    push_cast
    constructor <;> nlinarith [ht.1, ht.2]
  have hq := (residueColor_val N hN (a + i)).symm
  exact ⟨stripColor_eq_of_mem_strip N hN hh _ _ hq ht', _, hq, ht'.1, ht'.2⟩

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

/-- The discontinuous vertical selection is integrated strip by strip. -/
theorem verticalColumn_x_mean {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (hj : w j = 0)
    (G : PeriodGrid j) (hQ : G.rectangle.closed ⊆ sheetDomain w) :
    ‖(∫ p, verticalColumn hf w j (1, 0) p ∂G.rectangle.law) -
      (∫ p, column (globalSheet hf w) (1, 0) p ∂G.rectangle.law)‖ ≤
      2 * D / (widthFactor j : ℝ) := by
  obtain ⟨C, hF⟩ := globalSheet_lipschitz hf w
  choose C' hG using fun i : Fin (colors j) =>
    globalSheet_lipschitz hf (w.update j ((i : ℕ) + 1))
  let a : ℤ := G.ax * (colors j : ℤ)
  let n := G.nx * colors j
  have hn : 0 < n := Nat.mul_pos G.nx_pos (colors_pos j)
  have ha : (a : ℝ) * stripWidth j = G.ax * xPeriod j := by
    simp only [a, Int.cast_mul, Int.cast_natCast, xPeriod]; ring
  let c : Fin n → Fin (colors j) := fun i => residueColor (colors j) (colors_pos j) (a + i)
  let J := G.rectangle.y
  let Q' : Rectangle := ⟨Segment.grid (a * stripWidth j) (stripWidth j) n
    (stripWidth_pos j) hn, J⟩
  have hrect : Q' = G.rectangle := by
    have hx := G.rectangle_x_subdivided
    rw [← ha] at hx
    exact congrArg (fun I => Rectangle.mk I G.rectangle.y) hx.symm
  have hc : ∀ i : Fin n, ∀ x ∈ Ioo (Segment.cell (a * stripWidth j) (stripWidth j)
      (stripWidth_pos j) i).lo (Segment.cell (a * stripWidth j) (stripWidth j)
      (stripWidth_pos j) i).hi,
      stripColor (colors j) (colors_pos j) (stripWidth j) x = c i := by
    intro i x hx
    exact (color_on_cell _ _ (stripWidth_pos j) a i hx).1
  have hb : ∀ i : Fin n, ∀ x ∈ Ioo (Segment.cell (a * stripWidth j) (stripWidth j)
      (stripWidth_pos j) i).lo (Segment.cell (a * stripWidth j) (stripWidth j)
      (stripWidth_pos j) i).hi, ∀ y ∈ Ioo J.lo J.hi,
      ‖addedSheet hf w j (c i) (x, y) - globalSheet hf w (x, y)‖ ≤ D * scale j := by
    intro i x hx y hy
    have hxQ := Segment.cell_subset_grid (a * stripWidth j) (stripWidth j)
      (stripWidth_pos j) hn i ⟨hx.1.le, hx.2.le⟩
    have hp : (x, y) ∈ G.rectangle.closed := by
      rw [← hrect]
      exact ⟨hxQ, hy.1.le, hy.2.le⟩
    exact globalSheet_offset hf w j hj (c i).isLt (hQ hp)
      (Or.inr (color_on_cell _ _ (stripWidth_pos j) a i hx).2)
  have hm := horizontal_mean_bound_stripes (a * stripWidth j) (stripWidth j)
    (stripWidth_pos j) hn J hF hG (measurable_stripColor _ _ _) c hc hb
  change ‖(∫ p, verticalColumn hf w j (1, 0) p ∂Q'.law) -
    (∫ p, column (globalSheet hf w) (1, 0) p ∂Q'.law)‖ ≤ _ at hm
  rw [hrect] at hm
  convert hm using 1
  unfold stripWidth
  field_simp [ne_of_gt (scale_pos j)]

end VerticalStripeMean
end
end DoublingHilbert

end OAI

-- ---- platform node ----
open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem solution {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (hj : w j = 0)
    (G : PeriodGrid j) (hQ : G.rectangle.closed ⊆ sheetDomain w) :
    ‖(∫ p, verticalColumn hf w j (1, 0) p ∂G.rectangle.law) -
      (∫ p, column (globalSheet hf w) (1, 0) p ∂G.rectangle.law)‖ ≤
      2 * D / (widthFactor j : ℝ) := by
  first
    | exact OAI.DoublingHilbert.verticalColumn_x_mean hf w j hj G hQ
    | exact OAI.DoublingHilbert.verticalColumn_x_mean
    | (apply OAI.DoublingHilbert.verticalColumn_x_mean <;> assumption)
    | (intros; apply OAI.DoublingHilbert.verticalColumn_x_mean <;> assumption)
