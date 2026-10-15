-- Prove2me | solution 1 for OAI.DoublingHilbert.isOpen_sheetDomain
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:51:15.897702+00:00
-- url     : https://prove2.me/submissions/4f7e0cf6-4b95-4024-ad12-7cdfa41a5901

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Construction.lean:L84-L98
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.isOpen_sheetDomain. The node keeps its source
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

theorem isOpen_inColoredStrip (width : ℝ) (N i : ℕ) :
    IsOpen {t : ℝ | inColoredStrip width N i t} := by
  have h : {t : ℝ | inColoredStrip width N i t} =
      ⋃ (q : ℤ) (_ : q % (N : ℤ) = (i : ℤ)),
        Ioo ((q : ℝ) * width) (((q : ℝ) + 1) * width) := by
    ext t
    simp [inColoredStrip, and_left_comm]
  rw [h]
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_Ioo

theorem isOpen_allowed (j i : ℕ) : IsOpen {p : Base | allowed j i p} :=
  ((isOpen_inColoredStrip _ _ _).preimage continuous_snd).union
    ((isOpen_inColoredStrip _ _ _).preimage continuous_fst)

theorem isOpen_sheetDomain (w : Tuple) : IsOpen (sheetDomain w) := by
  classical
  by_cases hw : ∀ j ∈ w.support, w j ≤ colors j
  · have h : sheetDomain w = ⋂ j ∈ w.support, {p : Base | allowed j (w j - 1) p} := by
      ext p
      simp only [sheetDomain, mem_ofPred_eq, admissible, mem_iInter]
      exact ⟨fun h j hj => (h j hj).2, fun h j hj => ⟨hw j hj, h j hj⟩⟩
    rw [h]
    exact isOpen_biInter_finset fun j _ => isOpen_allowed j _
  · have h : sheetDomain w = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hw (fun j hj => (hp j hj).1)
    rw [h]
    exact isOpen_empty

end DoublingHilbert

end

end OAI

-- ---- platform node ----
open OAI OAI.DoublingHilbert
open scoped BigOperators
open Set

theorem solution (w : Tuple) : IsOpen (sheetDomain w) := by
  first
    | exact OAI.DoublingHilbert.isOpen_sheetDomain w
    | exact OAI.DoublingHilbert.isOpen_sheetDomain
    | (apply OAI.DoublingHilbert.isOpen_sheetDomain <;> assumption)
    | (intros; apply OAI.DoublingHilbert.isOpen_sheetDomain <;> assumption)
