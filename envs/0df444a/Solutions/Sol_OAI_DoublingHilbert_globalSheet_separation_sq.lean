-- Prove2me | solution 1 for OAI.DoublingHilbert.globalSheet_separation_sq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:09:40.839326+00:00
-- url     : https://prove2.me/submissions/3ba2108e-f8e4-47de-9609-f513140edc6c

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Grids.lean:L306-L324
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.globalSheet_separation_sq. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Theorems.Thm_OAI_DoublingHilbert_admissible_update_iff

-- ---- from OAI.Geometry.DoublingHilbert.Construction ----
namespace OAI

/-! Recurrent scales and orthogonal displacement sheets in real Hilbert space. -/

open scoped BigOperators
open Set

noncomputable section

namespace DoublingHilbert

theorem norm_levelVector_sub_sq (j i h : ℕ) (hih : i ≠ h) :
    ‖levelVector j i - levelVector j h‖ ^ 2 = 2 * (scale j) ^ 2 := by
  rw [norm_sub_sq_real]
  simp [hih]
  ring

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

/-- At a crossing two different permitted labels retain their exact Hilbert separation. -/
theorem globalSheet_separation_sq {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (hlower : ∀ x y, dist x y ≤ dist (f x) (f y))
    (w : Tuple) (j : ℕ) (hj : w j = 0) {i m : ℕ} (him : i ≠ m)
    (hi : i < colors j) (hm : m < colors j) {p : Base} (hp : p ∈ sheetDomain w)
    (hip : allowed j i p) (hmp : allowed j m p) :
    2 * scale j ^ 2 ≤ ‖globalSheet hf (w.update j (i + 1)) p -
      globalSheet hf (w.update j (m + 1)) p‖ ^ 2 := by
  have hup := (admissible_update_iff p w j i hj).mpr ⟨hp, hi, hip⟩
  have hmp' := (admissible_update_iff p w j m hj).mpr ⟨hp, hm, hmp⟩
  rw [globalSheet_eqOn hf _ hup, globalSheet_eqOn hf _ hmp',
    embeddingSheet_eq f _ p hup, embeddingSheet_eq f _ p hmp', ← dist_eq_norm]
  have hs : dist (⟨point p (w.update j (i + 1)), point_mem _ _ hup⟩ : constructedSet)
      ⟨point p (w.update j (m + 1)), point_mem _ _ hmp'⟩ ^ 2 = 2 * scale j ^ 2 := by
    change dist (point p (w.update j (i + 1))) (point p (w.update j (m + 1))) ^ 2 = _
    rw [point_update p w j i hj, point_update p w j m hj, dist_eq_norm,
      add_sub_add_left_eq_sub, norm_levelVector_sub_sq j i m him]
  rw [← hs]
  exact pow_le_pow_left₀ dist_nonneg (hlower _ _) 2

end SheetGeometry

end
end DoublingHilbert

end OAI

-- ---- platform node ----
open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem solution {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (hlower : ∀ x y, dist x y ≤ dist (f x) (f y))
    (w : Tuple) (j : ℕ) (hj : w j = 0) {i m : ℕ} (him : i ≠ m)
    (hi : i < colors j) (hm : m < colors j) {p : Base} (hp : p ∈ sheetDomain w)
    (hip : allowed j i p) (hmp : allowed j m p) :
    2 * scale j ^ 2 ≤ ‖globalSheet hf (w.update j (i + 1)) p -
      globalSheet hf (w.update j (m + 1)) p‖ ^ 2 := by
  first
    | exact OAI.DoublingHilbert.globalSheet_separation_sq hf hlower w j hj him hi hm hp hip hmp
    | exact OAI.DoublingHilbert.globalSheet_separation_sq
    | (apply OAI.DoublingHilbert.globalSheet_separation_sq <;> assumption)
    | (intros; apply OAI.DoublingHilbert.globalSheet_separation_sq <;> assumption)
