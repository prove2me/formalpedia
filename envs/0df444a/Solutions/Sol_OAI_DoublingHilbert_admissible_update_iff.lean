-- Prove2me | solution 1 for OAI.DoublingHilbert.admissible_update_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:52:20.538866+00:00
-- url     : https://prove2.me/submissions/f061fa55-780f-42d5-98ca-6433ec3ef64f

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Construction.lean:L177-L198
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.admissible_update_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction

-- ---- from OAI.Geometry.DoublingHilbert.Construction ----
namespace OAI

/-! Recurrent scales and orthogonal displacement sheets in real Hilbert space. -/

open scoped BigOperators
open Set

noncomputable section

namespace DoublingHilbert

theorem admissible_update_iff (p : Base) (w : Tuple) (j i : ℕ) (hj : w j = 0) :
    admissible p (w.update j (i + 1)) ↔
      admissible p w ∧ i < colors j ∧ allowed j i p := by
  classical
  have hjs : j ∉ w.support := by simpa using hj
  have hs := Finsupp.support_update_ne_zero w (a := j) (by omega : i + 1 ≠ 0)
  constructor
  · intro h
    have hjh := h j (by rw [hs]; exact Finset.mem_insert_self _ _)
    simp only [Finsupp.update_apply, ite_true, Nat.add_sub_cancel] at hjh
    refine ⟨?_, by omega, hjh.2⟩
    intro m hm
    have hmj : m ≠ j := by intro heq; subst m; exact hjs hm
    have hmh := h m (by rw [hs]; exact Finset.mem_insert_of_mem hm)
    simpa [Finsupp.update_apply, hmj] using hmh
  · rintro ⟨hw, hic, hip⟩ m hm
    rw [hs] at hm
    rcases Finset.mem_insert.mp hm with rfl | hm
    · simpa only [Finsupp.update_apply, ite_true, Nat.add_sub_cancel] using
        (show i + 1 ≤ colors m ∧ allowed m i p from ⟨by omega, hip⟩)
    · have hmj : m ≠ j := by intro heq; subst m; exact hjs hm
      simpa [Finsupp.update_apply, hmj] using hw m hm

end DoublingHilbert

end

end OAI

-- ---- platform node ----
open OAI OAI.DoublingHilbert
open scoped BigOperators
open Set

theorem solution (p : Base) (w : Tuple) (j i : ℕ) (hj : w j = 0) :
    admissible p (w.update j (i + 1)) ↔
      admissible p w ∧ i < colors j ∧ allowed j i p := by
  first
    | exact OAI.DoublingHilbert.admissible_update_iff p w j i hj
    | exact OAI.DoublingHilbert.admissible_update_iff
    | (apply OAI.DoublingHilbert.admissible_update_iff <;> assumption)
    | (intros; apply OAI.DoublingHilbert.admissible_update_iff <;> assumption)
