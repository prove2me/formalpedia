-- Prove2me | solution 1 for OAI.DoublingHilbert.exists_nearmax_grid
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:30:09.770255+00:00
-- url     : https://prove2.me/submissions/e141de53-1e87-446b-af27-06b7c877c64b

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Energy.lean:L218-L285
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.exists_nearmax_grid. The node keeps its source
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
import Theorems.Thm_OAI_DoublingHilbert_Rectangle_integral_le_four_of_subset
import Theorems.Thm_OAI_DoublingHilbert_Segment_exists_grid_inside
import Theorems.Thm_OAI_DoublingHilbert_goodSheetPoint_exists_rectangle
import Theorems.Thm_OAI_DoublingHilbert_isOpen_sheetDomain

-- ---- from OAI.Geometry.DoublingHilbert.Construction ----
namespace OAI

/-! Recurrent scales and orthogonal displacement sheets in real Hilbert space. -/

open scoped BigOperators
open Set

noncomputable section

namespace DoublingHilbert

theorem recurrent_parameters (N W J : ℕ) (hN : 0 < N) (hW : 0 < W) :
    ∃ j ≥ J, colors j = N ∧ widthFactor j = W := by
  refine ⟨Nat.pair (Nat.pair (N - 1) (W - 1)) J, Nat.right_le_pair _ _, ?_⟩
  simp only [colors, widthFactor, Nat.unpair_pair]
  omega

end DoublingHilbert

end

end OAI

-- ---- from OAI.Geometry.DoublingHilbert.Derivatives ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Derivative fields, good points, and the compact set of derivative norms. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

open MeasureTheory Set Filter
open scoped Topology

noncomputable section
namespace DoublingHilbert

section BoundedFields
variable {E : Type*} [NormedAddCommGroup E]

end BoundedFields

section DerivativeFields
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem norm_sheetColumn_le {f : ℝ × ℝ → E} {Ω : Set (ℝ × ℝ)}
    (hΩ : IsOpen Ω) {C : NNReal} (hf : LipschitzOnWith C f Ω) (v : ℝ × ℝ) (p : ℝ × ℝ) :
    ‖sheetColumn f Ω v p‖ ≤ C * ‖v‖ := by
  by_cases hp : p ∈ Ω
  · rw [sheetColumn, indicator_of_mem hp]
    exact ((fderiv ℝ f p).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hp) hf)
        (norm_nonneg v))
  · rw [sheetColumn, indicator_of_notMem hp, norm_zero]
    positivity

end DerivativeFields
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology

section Embedding
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem derivativePair_bounds {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (p : Base) :
    derivativePair f w p ∈ Icc (0, 0) ((2 * (D : ℝ)) ^ 2, (2 * (D : ℝ)) ^ 2) := by
  have hx := norm_sheetColumn_le (isOpen_sheetDomain w) (embeddingSheet_lipschitz hf w) (1, 0) p
  have hy := norm_sheetColumn_le (isOpen_sheetDomain w) (embeddingSheet_lipschitz hf w) (0, 1) p
  simp only [Prod.norm_def, norm_one, norm_zero, max_eq_left zero_le_one,
    max_eq_right zero_le_one, NNReal.coe_mul, NNReal.coe_ofNat, mul_one] at hx hy
  refine ⟨⟨sq_nonneg _, sq_nonneg _⟩, ?_⟩
  exact ⟨pow_le_pow_left₀ (norm_nonneg _) hx 2, pow_le_pow_left₀ (norm_nonneg _) hy 2⟩

end Embedding
end DoublingHilbert

open Set
noncomputable section
namespace DoublingHilbert

end DoublingHilbert

end
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

theorem const (e : E) : IsBoundedField (fun _ : X => e) :=
  ⟨stronglyMeasurable_const, ‖e‖, fun _ => le_rfl⟩

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

theorem scale_tendsto_zero : Tendsto scale atTop (𝓝 0) := by
  unfold scale
  exact (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(1000 : ℝ)⁻¹| < 1)).comp
    (tendsto_add_atTop_nat 1)

/-- Recurrence supplies arbitrarily fine unused levels with any prescribed pair. -/
theorem exists_fine_level (N W : ℕ) (hN : 0 < N) (hW : 0 < W) (w : Tuple)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ j, colors j = N ∧ widthFactor j = W ∧ w j = 0 ∧ scale j < ε := by
  classical
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (scale_tendsto_zero.eventually (gt_mem_nhds hε))
  obtain ⟨j, hj, hc, hw⟩ := recurrent_parameters N W (max J (w.support.sup id + 1)) hN hW
  have hnot : j ∉ w.support := by
    intro hmem
    have hmem' : j ≤ w.support.sup id := Finset.le_sup (f := id) hmem
    omega
  exact ⟨j, hc, hw, Finsupp.notMem_support_iff.mp hnot, hJ j (le_trans (le_max_left _ _) hj)⟩

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

theorem exists_inside (Q : Rectangle)
    (hx : xPeriod j < Q.x.length / 4) (hy : yPeriod j < Q.y.length / 4) :
    ∃ G : PeriodGrid j, G.rectangle.closed ⊆ Q.closed ∧
      Q.x.length / 2 ≤ G.rectangle.x.length ∧
      Q.y.length / 2 ≤ G.rectangle.y.length := by
  obtain ⟨ax, nx, hnx, hxl, hxr, hxs⟩ :=
    Q.x.exists_grid_inside (xPeriod_pos j) hx
  obtain ⟨ay, ny, hny, hyl, hyr, hys⟩ :=
    Q.y.exists_grid_inside (yPeriod_pos j) hy
  refine ⟨⟨ax, ay, nx, ny, hnx, hny⟩, ?_, hxs, hys⟩
  rintro p ⟨hp, hq⟩
  exact ⟨⟨hxl.trans hp.1, hp.2.trans hxr⟩, ⟨hyl.trans hq.1, hq.2.trans hyr⟩⟩

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

omit [CompleteSpace E] in
/-- Good points near the lexicographic pair and recurrence give actual fine grid rectangles. -/
theorem exists_nearmax_grid {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (N W : ℕ) (hN : 0 < N) (hW : 0 < W)
    {A B : ℝ} (hAB : (A, B) ∈ derivativeCompact f) {t : ℝ} (ht : 0 < t) :
    ∃ (w : Tuple) (j : ℕ) (G : PeriodGrid j) (u v : E),
      colors j = N ∧ widthFactor j = W ∧ w j = 0 ∧
      G.rectangle.closed ⊆ sheetDomain w ∧
      ‖u‖ ≤ 2 * D ∧ ‖v‖ ≤ 2 * D ∧
      A - ‖u‖ ^ 2 ≤ t ∧ B - ‖v‖ ^ 2 ≤ t ∧
      (∫ p, ‖column (globalSheet hf w) (1, 0) p - u‖ ^ 2 ∂G.rectangle.law) ≤ t ^ 2 ∧
      (∫ p, ‖column (globalSheet hf w) (0, 1) p - v‖ ^ 2 ∂G.rectangle.law) ≤ t ^ 2 ∧
      scale j / G.rectangle.x.length ≤ t ∧ scale j / G.rectangle.y.length ≤ t := by
  obtain ⟨z, ⟨w, p, hp, hpz⟩, hz⟩ := Metric.mem_closure_iff.mp hAB t ht
  subst z
  let u := sheetColumn (embeddingSheet f w) (sheetDomain w) (1, 0) p
  let v := sheetColumn (embeddingSheet f w) (sheetDomain w) (0, 1) p
  have hz' : |A - ‖u‖ ^ 2| < t ∧ |B - ‖v‖ ^ 2| < t := by
    simpa only [Prod.dist_eq, Real.dist_eq, max_lt_iff, derivativePair] using hz
  have hb := derivativePair_bounds hf w p
  have hu : ‖u‖ ≤ 2 * D :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hb.2.1
  have hv : ‖v‖ ≤ 2 * D :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hb.2.2
  obtain ⟨Q, hQ, hQu, hQv⟩ := goodSheetPoint_exists_rectangle hf hp
    (show 0 < t ^ 2 / 4 by positivity)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  let δ := min (Q.x.length / (4 * N * W))
    (min (Q.y.length / (4 * N)) (min (t * Q.x.length / 2) (t * Q.y.length / 2)))
  have hxpos := Q.x.length_pos
  have hypos := Q.y.length_pos
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨j, hjN, hjW, hjw, hjδ⟩ := exists_fine_level N W hN hW w hδ
  have hr₁ : scale j < Q.x.length / (4 * N * W) := hjδ.trans_le (min_le_left _ _)
  have hr₂ : scale j < Q.y.length / (4 * N) :=
    hjδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hr₃ : scale j < t * Q.x.length / 2 :=
    hjδ.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hr₄ : scale j < t * Q.y.length / 2 :=
    hjδ.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hxperiod : xPeriod j < Q.x.length / 4 := by
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * N * W)).mp hr₁
    dsimp [xPeriod, stripWidth]
    rw [hjN, hjW]
    nlinarith
  have hyperiod : yPeriod j < Q.y.length / 4 := by
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * N)).mp hr₂
    dsimp [yPeriod]
    rw [hjN]
    nlinarith
  obtain ⟨G, hGQ, hGx, hGy⟩ := PeriodGrid.exists_inside Q hxperiod hyperiod
  have bu := ((bounded_baseColumn hf w (1, 0)).sub (IsBoundedField.const u)).norm_sq
  have bv := ((bounded_baseColumn hf w (0, 1)).sub (IsBoundedField.const v)).norm_sq
  have hGu := Rectangle.integral_le_four_of_subset Q G.rectangle bu
    (fun _ => sq_nonneg _) hGQ hGx hGy
  have hGv := Rectangle.integral_le_four_of_subset Q G.rectangle bv
    (fun _ => sq_nonneg _) hGQ hGx hGy
  refine ⟨w, j, G, u, v, hjN, hjW, hjw, hGQ.trans hQ, hu, hv,
    (le_abs_self _).trans hz'.1.le, (le_abs_self _).trans hz'.2.le, ?_, ?_, ?_, ?_⟩
  · change (∫ p, ‖column (globalSheet hf w) (1, 0) p - u‖ ^ 2 ∂Q.law) < t ^ 2 / 4 at hQu
    linarith
  · change (∫ p, ‖column (globalSheet hf w) (0, 1) p - v‖ ^ 2 ∂Q.law) < t ^ 2 / 4 at hQv
    linarith
  · apply (div_le_iff₀ G.rectangle.x.length_pos).mpr
    nlinarith
  · apply (div_le_iff₀ G.rectangle.y.length_pos).mpr
    nlinarith

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

-- ---- platform node ----
open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
theorem solution {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (N W : ℕ) (hN : 0 < N) (hW : 0 < W)
    {A B : ℝ} (hAB : (A, B) ∈ derivativeCompact f) {t : ℝ} (ht : 0 < t) :
    ∃ (w : Tuple) (j : ℕ) (G : PeriodGrid j) (u v : E),
      colors j = N ∧ widthFactor j = W ∧ w j = 0 ∧
      G.rectangle.closed ⊆ sheetDomain w ∧
      ‖u‖ ≤ 2 * D ∧ ‖v‖ ≤ 2 * D ∧
      A - ‖u‖ ^ 2 ≤ t ∧ B - ‖v‖ ^ 2 ≤ t ∧
      (∫ p, ‖column (globalSheet hf w) (1, 0) p - u‖ ^ 2 ∂G.rectangle.law) ≤ t ^ 2 ∧
      (∫ p, ‖column (globalSheet hf w) (0, 1) p - v‖ ^ 2 ∂G.rectangle.law) ≤ t ^ 2 ∧
      scale j / G.rectangle.x.length ≤ t ∧ scale j / G.rectangle.y.length ≤ t := by
  first
    | exact OAI.DoublingHilbert.exists_nearmax_grid hf N W hN hW hAB ht
    | exact OAI.DoublingHilbert.exists_nearmax_grid
    | (apply OAI.DoublingHilbert.exists_nearmax_grid <;> assumption)
    | (intros; apply OAI.DoublingHilbert.exists_nearmax_grid <;> assumption)
