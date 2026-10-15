-- Prove2me | solution 1 for OAI.DoublingHilbert.exists_separated_family
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:43:04.273247+00:00
-- url     : https://prove2.me/submissions/857e0623-a398-4c89-8044-65544856d4a7

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Crossings.lean:L286-L363
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.exists_separated_family. The node keeps its source
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
import Theorems.Thm_OAI_DoublingHilbert_admissible_update_iff
import Theorems.Thm_OAI_DoublingHilbert_exists_color_column
import Theorems.Thm_OAI_DoublingHilbert_exists_color_row
import Theorems.Thm_OAI_DoublingHilbert_exists_small_energy_grid
import Theorems.Thm_OAI_DoublingHilbert_globalSheet_separation_sq

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

theorem integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Rectangle) (g : ℝ × ℝ → E) (hg : Integrable g Q.law) :
    (∫ p, g p ∂Q.law) = ∫ x, ∫ y, g (x, y) ∂Q.y.law ∂Q.x.law :=
  integral_prod g hg

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

theorem integral_snd {g : X × Y → E} (hg : IsBoundedField g) (ν : Measure Y)
    [IsProbabilityMeasure ν] : IsBoundedField (fun x => ∫ y, g (x, y) ∂ν) := by
  obtain ⟨M, hM⟩ := hg.2
  refine ⟨hg.1.integral_prod_right', M, fun x => ?_⟩
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall fun y => hM (x, y))

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

theorem exists_le_finite_mean {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) :
    ∃ i, v i ≤ (n : ℝ)⁻¹ * ∑ j, v j := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  by_contra! h
  have hs := Finset.sum_lt_sum_of_nonempty (s := Finset.univ) Finset.univ_nonempty
    (fun i _ => h i)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  rw [← mul_assoc, mul_inv_cancel₀ hn', one_mul] at hs
  exact lt_irrefl _ hs

namespace Segment

end Segment

namespace Rectangle

theorem exists_column_integral_le (a h : ℝ) {n : ℕ} (hh : 0 < h) (hn : 0 < n)
    (J : Segment) {g : ℝ × ℝ → ℝ} (hg : IsBoundedField g) :
    ∃ i : Fin n, (∫ p, g p ∂(Rectangle.mk (Segment.cell a h hh i) J).law) ≤
      (∫ p, g p ∂(Rectangle.mk (Segment.grid a h n hh hn) J).law) := by
  rw [integral_grid_x a h hh hn J hg, smul_eq_mul]
  exact exists_le_finite_mean hn _

theorem exists_row_integral_le (a h : ℝ) {n : ℕ} (hh : 0 < h) (hn : 0 < n)
    (I : Segment) {g : ℝ × ℝ → ℝ} (hg : IsBoundedField g) :
    ∃ i : Fin n, (∫ p, g p ∂(Rectangle.mk I (Segment.cell a h hh i)).law) ≤
      (∫ p, g p ∂(Rectangle.mk I (Segment.grid a h n hh hn)).law) := by
  rw [integral_grid_y a h hh hn I hg, smul_eq_mul]
  exact exists_le_finite_mean hn _

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

theorem block_subset (G : PeriodGrid j) (a : Fin G.nx) (b : Fin G.ny) :
    (G.block a b).closed ⊆ G.rectangle.closed := by
  rintro p ⟨hp, hq⟩
  exact ⟨Segment.cell_subset_grid _ _ (xPeriod_pos j) G.nx_pos a hp,
    Segment.cell_subset_grid _ _ (yPeriod_pos j) G.ny_pos b hq⟩

theorem exists_block_integral_le (G : PeriodGrid j) {g : Base → ℝ}
    (hg : IsBoundedField g) :
    ∃ a : Fin G.nx, ∃ b : Fin G.ny,
      (∫ p, g p ∂(G.block a b).law) ≤ ∫ p, g p ∂G.rectangle.law := by
  obtain ⟨a, ha⟩ := Rectangle.exists_column_integral_le _ _ (xPeriod_pos j) G.nx_pos
    G.rectangle.y hg
  obtain ⟨b, hb⟩ := Rectangle.exists_row_integral_le _ _ (yPeriod_pos j) G.ny_pos
    (Segment.cell (G.ax * xPeriod j) (xPeriod j) (xPeriod_pos j) a) hg
  exact ⟨a, b, hb.trans ha⟩

theorem block_x (G : PeriodGrid j) (a : Fin G.nx) (b : Fin G.ny) :
    (G.block a b).x = Segment.grid (((G.ax : ℝ) + a) * xPeriod j) (stripWidth j)
      (colors j) (stripWidth_pos j) (colors_pos j) := by
  apply Segment.ext
  · simp [block, Segment.cell, Segment.grid]; ring
  · simp [block, Segment.cell, Segment.grid, xPeriod]; ring

theorem block_y (G : PeriodGrid j) (a : Fin G.nx) (b : Fin G.ny) :
    (G.block a b).y = Segment.grid (((G.ay : ℝ) + b) * yPeriod j) (scale j)
      (colors j) (scale_pos j) (colors_pos j) := by
  apply Segment.ext
  · simp [block, Segment.cell, Segment.grid]; ring
  · simp [block, Segment.cell, Segment.grid, yPeriod]; ring

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

theorem column_subset (B : ColorBlock j) (i : Fin (colors j)) :
    Icc (B.column i).lo (B.column i).hi ⊆ Icc B.rectangle.x.lo B.rectangle.x.hi :=
  Segment.cell_subset_grid _ _ (stripWidth_pos j) (colors_pos j) i

theorem row_subset (B : ColorBlock j) (i : Fin (colors j)) :
    Icc (B.row i).lo (B.row i).hi ⊆ Icc B.rectangle.y.lo B.rectangle.y.hi :=
  Segment.cell_subset_grid _ _ (scale_pos j) (colors_pos j) i

theorem column_color (B : ColorBlock j) (i : Fin (colors j)) {x : ℝ}
    (hx : x ∈ Ioo (B.column i).lo (B.column i).hi) :
    stripColor (colors j) (colors_pos j) (stripWidth j) x = i ∧
      inColoredStrip (stripWidth j) (colors j) i x := by
  apply color_in_block _ _ (stripWidth_pos j) B.ax i
  simp only [column, Segment.cell, Nat.cast_add, Nat.cast_one, mem_Ioo] at hx
  dsimp [xPeriod] at hx
  constructor <;> nlinarith [hx.1, hx.2]

theorem row_color (B : ColorBlock j) (i : Fin (colors j)) {y : ℝ}
    (hy : y ∈ Ioo (B.row i).lo (B.row i).hi) :
    stripColor (colors j) (colors_pos j) (scale j) y = i ∧
      inColoredStrip (scale j) (colors j) i y := by
  apply color_in_block _ _ (scale_pos j) B.ay i
  simp only [row, Segment.cell, Nat.cast_add, Nat.cast_one, mem_Ioo] at hy
  dsimp [yPeriod] at hy
  constructor <;> nlinarith [hy.1, hy.2]

theorem x_length (B : ColorBlock j) :
    B.rectangle.x.length = (colors j : ℝ) * widthFactor j * scale j := by
  simp only [rectangle, Segment.grid_length, stripWidth]
  ring

theorem y_length (B : ColorBlock j) :
    B.rectangle.y.length = (colors j : ℝ) * scale j := by
  simp only [rectangle, Segment.grid_length]

end ColorBlock

namespace PeriodGrid
variable {j : ℕ}

theorem block_eq_colorBlock (G : PeriodGrid j) (a : Fin G.nx) (b : Fin G.ny) :
    G.block a b = (G.colorBlock a b).rectangle := by
  have hx := G.block_x a b
  have hy := G.block_y a b
  cases heq : G.block a b with
  | mk x y =>
    rw [heq] at hx hy
    simp only [Rectangle.mk.injEq, ColorBlock.rectangle, colorBlock]
    constructor
    · simpa only [Int.cast_add, Int.cast_natCast] using hx
    · simpa only [Int.cast_add, Int.cast_natCast] using hy

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

/-- Finite averaging chooses one complete period without increasing the mean energy. -/
theorem exists_small_energy_block {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (N : ℕ) (hN : 0 < N) {η : ℝ} (hη : 0 < η) :
    ∃ (w : Tuple) (j : ℕ) (B : ColorBlock j), colors j = N ∧ w j = 0 ∧
      B.rectangle.closed ⊆ sheetDomain w ∧
      (∫ p, combinedEnergy hf w j p ∂B.rectangle.law) < η := by
  obtain ⟨w, j, G, hjN, hjw, hQ, hE⟩ := exists_small_energy_grid hf N hN hη
  obtain ⟨a, b, hab⟩ := G.exists_block_integral_le (bounded_combinedEnergy hf w j)
  refine ⟨w, j, G.colorBlock a b, hjN, hjw, ?_, ?_⟩
  · rw [← G.block_eq_colorBlock a b]
    exact (G.block_subset a b).trans hQ
  · rw [← G.block_eq_colorBlock a b]
    exact hab.trans_lt hE

end BlockSelection
end DoublingHilbert

namespace DoublingHilbert

/-- The horizontal weight cancels exactly against the longer period side. -/
theorem small_oscillation_of_weighted_energy {n w r s e : ℝ}
    (hn : 0 < n) (hw : 0 < w) (hr : 0 < r) (hs : 0 ≤ s)
    (he : e ≤ 1 / (64 * n ^ 3))
    (hbound : w ^ 2 * s ^ 2 ≤ (n * w * r) ^ 2 * (n * e)) : s ≤ r / 8 := by
  have hright := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left he hn.le) (sq_nonneg (n * w * r))
  have heq : (n * w * r) ^ 2 * (n * (1 / (64 * n ^ 3))) = w ^ 2 * (r / 8) ^ 2 := by
    field_simp
    ring
  rw [heq] at hright
  have hsquared := (mul_le_mul_iff_right₀ (sq_pos_of_pos hw)).mp (hbound.trans hright)
  exact (sq_le_sq₀ hs (by positivity)).mp hsquared

section CrossingPacking
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Crossings of the selected lines force arbitrarily large separated families
in the fixed radius-D target ball. The lower bound is the genuine source distance. -/
theorem exists_separated_family {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (hlower : ∀ p q, dist p q ≤ dist (f p) (f q))
    (N : ℕ) (hN : 0 < N) :
    ∃ z : Fin N → E, (∀ i, ‖z i‖ ≤ D) ∧
      ∀ i m, i ≠ m → 1 ≤ dist (z i) (z m) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨w, j, B, hjN, hjw, hB, henergy⟩ := exists_small_energy_block hf N hN
    (show 0 < 1 / (64 * (N : ℝ) ^ 3) by positivity)
  subst N
  choose y hy hyo using fun i => exists_color_row hf w j B i
  choose x hx hxo using fun i => exists_color_column hf w j B i
  have hxc (i) : x i ∈ Icc B.rectangle.x.lo B.rectangle.x.hi :=
    B.column_subset i ⟨(hx i).1.le, (hx i).2.le⟩
  have hyc (i) : y i ∈ Icc B.rectangle.y.lo B.rectangle.y.hi :=
    B.row_subset i ⟨(hy i).1.le, (hy i).2.le⟩
  let h (i : Fin (colors j)) (p : Base) := addedSheet hf w j i p - globalSheet hf w p
  let p (i : Fin (colors j)) : Base := (x i, y i)
  have hr := scale_pos j
  have hWR : (0 : ℝ) < widthFactor j := by exact_mod_cast widthFactor_pos j
  have hrow (i m : Fin (colors j)) :
      ‖h i (x m, y i) - h i (p i)‖ ≤ scale j / 8 := by
    apply small_oscillation_of_weighted_energy hNR hWR hr (norm_nonneg _) henergy.le
    have ho := hyo i (x i) (hxc i) (x m) (hxc m)
    rw [B.x_length] at ho
    exact ho
  have hcolumn (i m : Fin (colors j)) :
      ‖h m (x m, y i) - h m (p m)‖ ≤ scale j / 8 := by
    apply small_oscillation_of_weighted_energy (w := 1) hNR zero_lt_one hr
      (norm_nonneg _) henergy.le
    have ho := hxo m (y m) (hyc m) (y i) (hyc i)
    rw [B.y_length] at ho
    simpa only [one_pow, one_mul, mul_one] using ho
  have hcentral (i m : Fin (colors j)) (him : i ≠ m) :
      scale j ≤ ‖h i (p i) - h m (p m)‖ := by
    let c : Base := (x m, y i)
    have hiAllowed : allowed j i c := Or.inl (B.row_color i (hy i)).2
    have hmAllowed : allowed j m c := Or.inr (B.column_color m (hx m)).2
    have hsep := globalSheet_separation_sq hf hlower w j hjw
      (show (i : ℕ) ≠ (m : ℕ) from fun heq => him (Fin.ext heq))
      i.isLt m.isLt (hB ⟨hxc m, hyc i⟩) hiAllowed hmAllowed
    have hdiff : h i c - h m c = addedSheet hf w j i c - addedSheet hf w j m c := by
      dsimp [h]
      abel
    change 2 * scale j ^ 2 ≤ ‖addedSheet hf w j i c - addedSheet hf w j m c‖ ^ 2 at hsep
    rw [← hdiff] at hsep
    have ht₁ := dist_triangle (h i c) (h i (p i)) (h m c)
    have ht₂ := dist_triangle (h i (p i)) (h m (p m)) (h m c)
    simp only [dist_eq_norm] at ht₁ ht₂
    have hv := hcolumn i m
    have hv' : ‖h m (p m) - h m c‖ ≤ scale j / 8 := by
      simpa only [c, norm_sub_rev] using hv
    have hh := hrow i m
    change ‖h i c - h i (p i)‖ ≤ scale j / 8 at hh
    by_contra hn
    have hm : ‖h i (p i) - h m (p m)‖ < scale j := lt_of_not_ge hn
    have hbound : ‖h i c - h m c‖ ≤ 5 * scale j / 4 := by linarith
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hbound 2
    nlinarith [sq_pos_of_pos hr]
  let z (i : Fin (colors j)) : E := (scale j)⁻¹ • h i (p i)
  refine ⟨z, ?_, ?_⟩
  · intro i
    have hoff := globalSheet_offset hf w j hjw i.isLt (p := p i) (hB ⟨hxc i, hyc i⟩)
      (Or.inl (B.row_color i (hy i)).2)
    change ‖h i (p i)‖ ≤ D * scale j at hoff
    dsimp [z]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    calc
      _ ≤ (scale j)⁻¹ * (D * scale j) := mul_le_mul_of_nonneg_left hoff (inv_nonneg.mpr hr.le)
      _ = D := by field_simp
  · intro i m him
    rw [dist_eq_norm]
    dsimp [z]
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    calc
      1 = (scale j)⁻¹ * scale j := (inv_mul_cancel₀ hr.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcentral i m him) (inv_nonneg.mpr hr.le)

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
    (hf : LipschitzWith D f) (hlower : ∀ p q, dist p q ≤ dist (f p) (f q))
    (N : ℕ) (hN : 0 < N) :
    ∃ z : Fin N → E, (∀ i, ‖z i‖ ≤ D) ∧
      ∀ i m, i ≠ m → 1 ≤ dist (z i) (z m) := by
  first
    | exact OAI.DoublingHilbert.exists_separated_family hf hlower N hN
    | exact OAI.DoublingHilbert.exists_separated_family
    | (apply OAI.DoublingHilbert.exists_separated_family <;> assumption)
    | (intros; apply OAI.DoublingHilbert.exists_separated_family <;> assumption)
