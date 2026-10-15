-- Prove2me | solution 1 for OAI.DoublingHilbert.verticalColumn_y_mean
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:18:34.59704+00:00
-- url     : https://prove2.me/submissions/22a9e549-063e-47ca-be32-2b71f4c02799

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/SelectedSheets.lean:L319-L338
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.verticalColumn_y_mean. The node keeps its source
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
import Theorems.Thm_OAI_DoublingHilbert_vertical_mean_bound

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

theorem measurable_stripColor (N : ℕ) (hN : 0 < N) (h : ℝ) :
    Measurable (stripColor N hN h) := by
  let c : ℤ → Fin N := fun z => ⟨(z % (N : ℤ)).toNat, by
    have hnonneg := Int.emod_nonneg z (by exact_mod_cast hN.ne' : (N : ℤ) ≠ 0)
    have hlt := Int.emod_lt_of_pos z (by exact_mod_cast hN : (0 : ℤ) < N)
    exact_mod_cast (Int.toNat_lt hnonneg).mpr hlt⟩
  exact (measurable_of_countable c).comp
    (Int.measurable_floor.comp (measurable_id.div_const h))

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

theorem verticalColumn_y_mean {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (hj : w j = 0)
    (Q : Rectangle) (hQ : Q.closed ⊆ sheetDomain w) :
    ‖(∫ p, verticalColumn hf w j (0, 1) p ∂Q.law) -
      (∫ p, column (globalSheet hf w) (0, 1) p ∂Q.law)‖ ≤
      2 * D * scale j / Q.y.length := by
  obtain ⟨C, hF⟩ := globalSheet_lipschitz hf w
  choose C' hG using fun i : Fin (colors j) =>
    globalSheet_lipschitz hf (w.update j ((i : ℕ) + 1))
  have hend : ∀ y ∈ Icc Q.y.lo Q.y.hi, ∀ᵐ x ∂Q.x.law,
      ‖addedSheet hf w j (stripColor (colors j) (colors_pos j) (stripWidth j) x) (x, y) -
        globalSheet hf w (x, y)‖ ≤ D * scale j := by
    intro y hy
    filter_upwards [Q.x.ae_mem,
      Q.x.ae_of_ae (ae_inColoredStrip_stripColor _ _ (stripWidth_pos j))] with x hx hc
    exact globalSheet_offset hf w j hj (stripColor _ _ _ _).isLt
      (hQ ⟨⟨hx.1.le, hx.2.le⟩, hy⟩) (Or.inr hc)
  simpa only [mul_assoc, verticalColumn, addedSheet] using vertical_mean_bound Q hF hG
    (measurable_stripColor _ _ _) (hend _ ⟨le_rfl, Q.y.lt.le⟩)
      (hend _ ⟨Q.y.lt.le, le_rfl⟩)

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
    ‖(∫ p, verticalColumn hf w j (0, 1) p ∂Q.law) -
      (∫ p, column (globalSheet hf w) (0, 1) p ∂Q.law)‖ ≤
      2 * D * scale j / Q.y.length := by
  first
    | exact OAI.DoublingHilbert.verticalColumn_y_mean hf w j hj Q hQ
    | exact OAI.DoublingHilbert.verticalColumn_y_mean
    | (apply OAI.DoublingHilbert.verticalColumn_y_mean <;> assumption)
    | (intros; apply OAI.DoublingHilbert.verticalColumn_y_mean <;> assumption)
