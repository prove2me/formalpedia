-- Prove2me | solution 1 for OAI.DoublingHilbert.exists_small_energy_grid
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:34:18.453196+00:00
-- url     : https://prove2.me/submissions/828de102-da29-4aac-84fb-db1b0b43c7b1

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Energy.lean:L328-L362
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.exists_small_energy_grid. The node keeps its source
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
import Theorems.Thm_OAI_DoublingHilbert_IsBoundedField_select
import Theorems.Thm_OAI_DoublingHilbert_ae_tendsto_average_norm_sub_sq
import Theorems.Thm_OAI_DoublingHilbert_anisotropic_energy_bound
import Theorems.Thm_OAI_DoublingHilbert_exists_energy_parameters
import Theorems.Thm_OAI_DoublingHilbert_exists_nearmax_grid
import Theorems.Thm_OAI_DoublingHilbert_isOpen_sheetDomain
import Theorems.Thm_OAI_DoublingHilbert_lexicographic_affine_barrier

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

theorem aestronglyMeasurable_sheetColumn (f : ℝ × ℝ → E) {Ω : Set (ℝ × ℝ)}
    (hΩ : IsOpen Ω) (v : ℝ × ℝ) :
    AEStronglyMeasurable (sheetColumn f Ω v) volume := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  apply AEStronglyMeasurable.indicator _ hΩ.measurableSet
  exact ((ContinuousLinearMap.apply ℝ E v).continuous.measurable.comp
    (measurable_fderiv ℝ f)).aestronglyMeasurable

/-- Good derivative points have full measure on every sheet. -/
theorem ae_good_sheet_points {f : ℝ × ℝ → E} {Ω : Set (ℝ × ℝ)}
    (hΩ : IsOpen Ω) {C : NNReal} (hf : LipschitzOnWith C f Ω) (v₁ v₂ : ℝ × ℝ) :
    ∀ᵐ p, p ∈ Ω → DifferentiableAt ℝ f p ∧
      Tendsto (fun r : ℝ => ⨍ q in Metric.closedBall p r,
        ‖sheetColumn f Ω v₁ q - sheetColumn f Ω v₁ p‖ ^ 2)
        (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun r : ℝ => ⨍ q in Metric.closedBall p r,
        ‖sheetColumn f Ω v₂ q - sheetColumn f Ω v₂ p‖ ^ 2)
        (𝓝[>] 0) (𝓝 0) := by
  have h₁ := ae_tendsto_average_norm_sub_sq (aestronglyMeasurable_sheetColumn f hΩ v₁)
    (mul_nonneg C.coe_nonneg (norm_nonneg v₁)) (norm_sheetColumn_le hΩ hf v₁)
  have h₂ := ae_tendsto_average_norm_sub_sq (aestronglyMeasurable_sheetColumn f hΩ v₂)
    (mul_nonneg C.coe_nonneg (norm_nonneg v₂)) (norm_sheetColumn_le hΩ hf v₂)
  filter_upwards [hf.ae_differentiableWithinAt_of_mem (μ := volume), h₁, h₂] with p hp h₁p h₂p hpm
  exact ⟨(hp hpm).differentiableAt (hΩ.mem_nhds hpm), h₁p, h₂p⟩

end DerivativeFields
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology

section Embedding
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem ae_good_embeddingSheet {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) :
    ∀ᵐ p, p ∈ sheetDomain w → goodSheetPoint f w p := by
  filter_upwards [ae_good_sheet_points (isOpen_sheetDomain w) (embeddingSheet_lipschitz hf w)
    (1, 0) (0, 1)] with p hp hmem
  exact ⟨hmem, hp hmem⟩

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

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem derivativeCompact_subset {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) :
    derivativeCompact f ⊆ Icc (0, 0) ((2 * (D : ℝ)) ^ 2, (2 * (D : ℝ)) ^ 2) := by
  apply closure_minimal _ isClosed_Icc
  rintro z ⟨w, p, _, rfl⟩
  exact derivativePair_bounds hf w p

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem isCompact_derivativeCompact {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) : IsCompact (derivativeCompact f) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (derivativeCompact_subset hf)

theorem derivativeData_nonempty {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) : (derivativeData f).Nonempty := by
  obtain ⟨p, hp⟩ := (ae_good_embeddingSheet hf 0).exists
  exact ⟨derivativePair f 0 p, 0, p, hp (admissible_zero p), rfl⟩

theorem derivativeCompact_nonempty {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) : (derivativeCompact f).Nonempty :=
  (derivativeData_nonempty hf).mono subset_closure

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

theorem measurable_stripColor (N : ℕ) (hN : 0 < N) (h : ℝ) :
    Measurable (stripColor N hN h) := by
  let c : ℤ → Fin N := fun z => ⟨(z % (N : ℤ)).toNat, by
    have hnonneg := Int.emod_nonneg z (by exact_mod_cast hN.ne' : (N : ℤ) ≠ 0)
    have hlt := Int.emod_lt_of_pos z (by exact_mod_cast hN : (0 : ℤ) < N)
    exact_mod_cast (Int.toNat_lt hnonneg).mpr hlt⟩
  exact (measurable_of_countable c).comp
    (Int.measurable_floor.comp (measurable_id.div_const h))

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

-- ---- from OAI.Geometry.DoublingHilbert.Extremal ----
namespace OAI

/-! Compact lexicographic extrema and quantitative second-moment estimates. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DoublingHilbert
/-- A nonempty compact set has a lexicographic maximum. -/
theorem exists_lexicographic_maximum {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ A B : ℝ, (A, B) ∈ K ∧
      (∀ p ∈ K, p.1 ≤ A) ∧ (∀ p ∈ K, p.1 = A → p.2 ≤ B) := by
  obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn hne continuous_fst.continuousOn
  let fiber : Set (ℝ × ℝ) := K ∩ {q | q.1 = p.1}
  have hc : IsCompact fiber :=
    hK.inter_right (isClosed_eq continuous_fst continuous_const)
  obtain ⟨q, hq, hqmax⟩ := hc.exists_isMaxOn ⟨p, hp, rfl⟩ continuous_snd.continuousOn
  refine ⟨p.1, q.2, ?_, hmax, ?_⟩
  · have hqfst : q.1 = p.1 := hq.2
    simpa only [← hqfst, Prod.eta] using hq.1
  · intro r hr hrp
    exact hqmax ⟨hr, hrp⟩

open MeasureTheory
open scoped BigOperators

section Moments

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [IsProbabilityMeasure μ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

end Moments

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

/-- The full analytic output: arbitrarily small combined energy on actual sheets
of the single fixed Hilbert set, at a level with any prescribed number of colors. -/
theorem exists_small_energy_grid {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (N : ℕ) (hN : 0 < N) {η : ℝ} (hη : 0 < η) :
    ∃ (w : Tuple) (j : ℕ) (G : PeriodGrid j), colors j = N ∧ w j = 0 ∧
      G.rectangle.closed ⊆ sheetDomain w ∧
      (∫ p, combinedEnergy hf w j p ∂G.rectangle.law) < η := by
  obtain ⟨A, B, hAB, hfirst, hsecond⟩ := exists_lexicographic_maximum
    (isCompact_derivativeCompact hf) (derivativeCompact_nonempty hf)
  have hb := derivativeCompact_subset hf hAB
  obtain ⟨C, hC, hbarrier⟩ := lexicographic_affine_barrier (isCompact_derivativeCompact hf)
    hfirst hsecond (fun z hz => (derivativeCompact_subset hf hz).2.2) hb.1.2
    (sq_nonneg (2 * (D : ℝ))) (show 0 < η / 8 by positivity)
  obtain ⟨W, hW, t, ht, ht1, hparam⟩ := exists_energy_parameters D.coe_nonneg hC hη
  obtain ⟨w, j, G, u, v, hjN, hjW, hjw, hQ, hu, hv, hnu, hnv, hbu, hbv, hrx, hry⟩ :=
    exists_nearmax_grid hf N W hN hW hAB ht
  obtain ⟨hH, hV⟩ := anisotropic_energy_bound hf w j hjw G hQ hC ht.le ht1
    hfirst hbarrier u v hu hv hnu hnv hbu hbv hrx hry
  rw [hjW] at hV
  have hH' := mul_le_mul_of_nonneg_left hH (sq_nonneg (W : ℝ))
  have bH := bounded_horizontalEnergy hf w j
  have bV := bounded_verticalEnergy hf w j
  refine ⟨w, j, G, hjN, hjw, hQ, ?_⟩
  calc
    (∫ p, combinedEnergy hf w j p ∂G.rectangle.law) =
        (W : ℝ) ^ 2 * (∫ p, horizontalEnergy hf w j p ∂G.rectangle.law) +
          (∫ p, verticalEnergy hf w j p ∂G.rectangle.law) := by
      unfold combinedEnergy
      rw [integral_add ((bH.const_mul _).integrable _) (bV.integrable _), integral_const_mul, hjW]
    _ ≤ (W : ℝ) ^ 2 * (horizontalCoefficient D * t) +
        (2 * (η / 8) + 16 * C * (D : ℝ) ^ 2 / (W : ℝ) + verticalCoefficient D C * t) :=
      add_le_add hH' hV
    _ = 2 * (η / 8) + 16 * C * (D : ℝ) ^ 2 / (W : ℝ) +
        ((W : ℝ) ^ 2 * horizontalCoefficient D + verticalCoefficient D C) * t := by ring
    _ < η := hparam

end SmallEnergy
end
end DoublingHilbert

end OAI

-- ---- platform node ----
open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem solution {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (N : ℕ) (hN : 0 < N) {η : ℝ} (hη : 0 < η) :
    ∃ (w : Tuple) (j : ℕ) (G : PeriodGrid j), colors j = N ∧ w j = 0 ∧
      G.rectangle.closed ⊆ sheetDomain w ∧
      (∫ p, combinedEnergy hf w j p ∂G.rectangle.law) < η := by
  first
    | exact OAI.DoublingHilbert.exists_small_energy_grid hf N hN hη
    | exact OAI.DoublingHilbert.exists_small_energy_grid
    | (apply OAI.DoublingHilbert.exists_small_energy_grid <;> assumption)
    | (intros; apply OAI.DoublingHilbert.exists_small_energy_grid <;> assumption)
