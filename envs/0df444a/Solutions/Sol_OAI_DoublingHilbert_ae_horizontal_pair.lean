-- Prove2me | solution 1 for OAI.DoublingHilbert.ae_horizontal_pair
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:13:09.71046+00:00
-- url     : https://prove2.me/submissions/1434cb14-32a4-4466-914c-a68c7086c4d1

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/SelectedSheets.lean:L263-L278
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.ae_horizontal_pair. The node keeps its source
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
import Theorems.Thm_OAI_DoublingHilbert_ae_tendsto_average_norm_sub_sq
import Theorems.Thm_OAI_DoublingHilbert_isOpen_sheetDomain

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

theorem ae_globalSheet_pair {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) :
    ∀ᵐ p, p ∈ sheetDomain w →
      (‖column (globalSheet hf w) (1, 0) p‖ ^ 2,
       ‖column (globalSheet hf w) (0, 1) p‖ ^ 2) ∈ derivativeCompact f := by
  filter_upwards [ae_good_embeddingSheet hf w] with p hp hmem
  rw [column_globalSheet hf w hmem, column_globalSheet hf w hmem]
  exact subset_closure ⟨w, p, hp hmem, rfl⟩

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

theorem ae_mem (Q : Rectangle) : ∀ᵐ p ∂Q.law, p ∈ Q.interior := by
  exact ((Measure.quasiMeasurePreserving_fst.ae Q.x.ae_mem).and
    (Measure.quasiMeasurePreserving_snd.ae Q.y.ae_mem))

theorem ae_of_ae (Q : Rectangle) {P : ℝ × ℝ → Prop} (hP : ∀ᵐ p, P p) :
    ∀ᵐ p ∂Q.law, P p := by
  rw [Measure.volume_eq_prod] at hP
  have hx : Q.x.law ≪ volume := Measure.absolutelyContinuous_restrict.smul_left _
  have hy : Q.y.law ≪ volume := Measure.absolutelyContinuous_restrict.smul_left _
  exact (hx.prod hy).ae_le hP

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

theorem inColoredStrip_stripColor (N : ℕ) (hN : 0 < N) {h t : ℝ} (hh : 0 < h)
    (ht : ∀ q : ℤ, t ≠ (q : ℝ) * h) :
    inColoredStrip h N (stripColor N hN h t) t := by
  refine ⟨⌊t / h⌋, ?_, ?_, ?_⟩
  · simp only [stripColor]
    exact (Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hN.ne'))).symm
  · have hle := (le_div_iff₀ hh).mp (Int.floor_le (t / h))
    exact lt_of_le_of_ne hle (ht _).symm
  · exact (div_lt_iff₀ hh).mp (Int.lt_floor_add_one (t / h))

theorem ae_inColoredStrip_stripColor (N : ℕ) (hN : 0 < N) {h : ℝ} (hh : 0 < h) :
    ∀ᵐ t, inColoredStrip h N (stripColor N hN h t) t := by
  filter_upwards [ae_all_iff.mpr (fun q : ℤ => volume.ae_ne ((q : ℝ) * h))] with t ht
  exact inColoredStrip_stripColor N hN hh ht

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

end PeriodGrid

end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

namespace Rectangle

theorem interior_subset_closed (Q : Rectangle) : Q.interior ⊆ Q.closed := by
  rintro p ⟨hp, hq⟩
  exact ⟨⟨hp.1.le, hp.2.le⟩, ⟨hq.1.le, hq.2.le⟩⟩

end Rectangle

section SelectedSheets
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem ae_horizontal_pair {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (hj : w j = 0)
    (Q : Rectangle) (hQ : Q.closed ⊆ sheetDomain w) :
    ∀ᵐ p ∂Q.law, (‖horizontalColumn hf w j (1, 0) p‖ ^ 2,
      ‖horizontalColumn hf w j (0, 1) p‖ ^ 2) ∈ derivativeCompact f := by
  have hg : ∀ᵐ p, ∀ i : Fin (colors j), p ∈ sheetDomain (w.update j ((i : ℕ) + 1)) →
      (‖column (addedSheet hf w j i) (1, 0) p‖ ^ 2,
       ‖column (addedSheet hf w j i) (0, 1) p‖ ^ 2) ∈ derivativeCompact f :=
    ae_all_iff.mpr fun i => ae_globalSheet_pair hf _
  have hs : ∀ᵐ p ∂Q.law,
      inColoredStrip (scale j) (colors j) (stripColor (colors j) (colors_pos j) (scale j) p.2) p.2 :=
    Measure.quasiMeasurePreserving_snd.ae
      (Q.y.ae_of_ae (ae_inColoredStrip_stripColor _ _ (scale_pos j)))
  filter_upwards [Q.ae_of_ae hg, Q.ae_mem, hs] with p hp hmem hstrip
  exact hp _ ((admissible_update_iff p w j _ hj).mpr
    ⟨hQ (Q.interior_subset_closed hmem), (stripColor _ _ _ _).isLt, Or.inl hstrip⟩)

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem solution {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (hj : w j = 0)
    (Q : Rectangle) (hQ : Q.closed ⊆ sheetDomain w) :
    ∀ᵐ p ∂Q.law, (‖horizontalColumn hf w j (1, 0) p‖ ^ 2,
      ‖horizontalColumn hf w j (0, 1) p‖ ^ 2) ∈ derivativeCompact f := by
  first
    | exact OAI.DoublingHilbert.ae_horizontal_pair hf w j hj Q hQ
    | exact OAI.DoublingHilbert.ae_horizontal_pair
    | (apply OAI.DoublingHilbert.ae_horizontal_pair <;> assumption)
    | (intros; apply OAI.DoublingHilbert.ae_horizontal_pair <;> assumption)
