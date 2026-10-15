-- Prove2me | solution 1 for OAI.DoublingHilbert.isCompact_exists_packing_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:46:35.207151+00:00
-- url     : https://prove2.me/submissions/df4b8765-efb2-446b-beb8-41ba77e52fe6

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Doubling.lean:L100-L126
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.isCompact_exists_packing_bound. The node keeps its source
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

/-- Compact metric sets admit a finite upper bound for any fixed positive separation. -/
theorem isCompact_exists_packing_bound {X : Type*} [PseudoMetricSpace X]
    {s : Set X} (hs : IsCompact s) {r : ℝ} (hr : 0 < r) :
    ∃ bound : ℕ, ∀ {n : ℕ} (z : Fin n → X), (∀ i, z i ∈ s) →
      (∀ i j, i ≠ j → r ≤ dist (z i) (z j)) → n ≤ bound := by
  classical
  obtain ⟨t, _, ht, hcover⟩ := hs.finite_cover_balls (show 0 < r / 2 by positivity)
  let := ht.fintype
  refine ⟨Fintype.card t, ?_⟩
  intro n z hz hsep
  have hex : ∀ i, ∃ c : t, dist (z i) c < r / 2 := by
    intro i
    have hi := hcover (hz i)
    simp only [mem_iUnion, mem_ball] at hi
    obtain ⟨c, hc, hdist⟩ := hi
    exact ⟨⟨c, hc⟩, hdist⟩
  choose c hc using hex
  have hinj : Function.Injective c := by
    intro i j hij
    by_contra hne
    have hj := hc j
    rw [← hij] at hj
    have hd := dist_triangle (z i) (c i : X) (z j)
    rw [dist_comm (c i : X) (z j)] at hd
    have hi := hc i
    linarith [hsep i j hne]
  simpa using Fintype.card_le_of_injective c hinj

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

theorem solution {X : Type*} [PseudoMetricSpace X]
    {s : Set X} (hs : IsCompact s) {r : ℝ} (hr : 0 < r) :
    ∃ bound : ℕ, ∀ {n : ℕ} (z : Fin n → X), (∀ i, z i ∈ s) →
      (∀ i j, i ≠ j → r ≤ dist (z i) (z j)) → n ≤ bound := by
  first
    | exact OAI.DoublingHilbert.isCompact_exists_packing_bound hs hr
    | exact OAI.DoublingHilbert.isCompact_exists_packing_bound
    | (apply OAI.DoublingHilbert.isCompact_exists_packing_bound <;> assumption)
    | (intros; apply OAI.DoublingHilbert.isCompact_exists_packing_bound <;> assumption)
