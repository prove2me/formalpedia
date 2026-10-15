-- Prove2me | solution 1 for OAI.DoublingHilbert.cover_of_finite_code
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:44:52.154915+00:00
-- url     : https://prove2.me/submissions/720cb184-9e32-4ba1-8759-b4a63052b8c3

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Doubling.lean:L75-L98
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.cover_of_finite_code. The node keeps its source
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
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling

-- ---- from OAI.Geometry.DoublingHilbert.Doubling ----
namespace OAI

open MeasureTheory Set Filter
open scoped BigOperators Topology

/-! Intrinsic doubling of the same fixed Hilbert subset. -/

open Set
noncomputable section
namespace DoublingHilbert

end DoublingHilbert

open Set Metric
noncomputable section
namespace DoublingHilbert

/-- A finite coding with fibers of small diameter supplies intrinsic covering centers. -/
theorem cover_of_finite_code {X I : Type*} [PseudoMetricSpace X] [Fintype I]
    (s : Set X) (code : s → I) {r : ℝ}
    (hcode : ∀ x y : s, code x = code y → dist (x : X) (y : X) < r) :
    ∃ centers : Finset X, centers.card ≤ Fintype.card I ∧
      (↑centers : Set X) ⊆ s ∧ ∀ x ∈ s, ∃ y ∈ centers, dist x y < r := by
  classical
  let used : Finset I := Finset.univ.filter (fun i => ∃ x, code x = i)
  let representative : (i : I) → i ∈ used → s := fun i hi =>
    Classical.choose (Finset.mem_filter.mp hi).2
  have hrep : ∀ i hi, code (representative i hi) = i := fun i hi =>
    Classical.choose_spec (Finset.mem_filter.mp hi).2
  let centers : Finset X := used.attach.image (fun i : {i // i ∈ used} => (representative i.val i.prop : X))
  refine ⟨centers, ?_, ?_, ?_⟩
  · exact (Finset.card_image_le).trans (by simpa only [Finset.card_attach] using Finset.card_le_univ used)
  · intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact (representative i i.prop).prop
  · intro x hx
    let xx : s := ⟨x, hx⟩
    have hmem : code xx ∈ used := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨xx, rfl⟩⟩
    refine ⟨representative (code xx) hmem, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨⟨code xx, hmem⟩, Finset.mem_attach _ _, rfl⟩
    · exact hcode xx (representative (code xx) hmem) (hrep (code xx) hmem).symm

end DoublingHilbert

namespace DoublingHilbert
open Set
open scoped BigOperators

end DoublingHilbert

end
end

end OAI

-- ---- platform node ----
open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Set
open Set Metric

theorem solution {X I : Type*} [PseudoMetricSpace X] [Fintype I]
    (s : Set X) (code : s → I) {r : ℝ}
    (hcode : ∀ x y : s, code x = code y → dist (x : X) (y : X) < r) :
    ∃ centers : Finset X, centers.card ≤ Fintype.card I ∧
      (↑centers : Set X) ⊆ s ∧ ∀ x ∈ s, ∃ y ∈ centers, dist x y < r := by
  first
    | exact OAI.DoublingHilbert.cover_of_finite_code s code hcode
    | exact OAI.DoublingHilbert.cover_of_finite_code
    | (apply OAI.DoublingHilbert.cover_of_finite_code <;> assumption)
    | (intros; apply OAI.DoublingHilbert.cover_of_finite_code <;> assumption)
