-- Prove2me | solution 1 for OAI.Barnette.PlaneEmbedding.uniform_thickening
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T05:08:59.394782+00:00
-- url     : https://prove2.me/submissions/f87c13e7-8bad-43dd-bced-c3ab2bd295b3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Traces.lean:L240-L255
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.PlaneEmbedding.uniform_thickening. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Forest
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Contraction
import Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorDuality
import Definitions.Def_OAI_Combinatorics_Hamiltonian_BMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Matching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ForestMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ThreeCuts
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Gluing
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Traces

-- ---- from OAI.Combinatorics.Hamiltonian.Traces ----
namespace OAI

/-! Compact connected arc traces and uniform positive thickenings. -/

namespace Barnette.PlaneEmbedding

noncomputable section

variable {V : Type*} {G : SimpleGraph V} (E : PlaneEmbedding G)

theorem finite_positive_radius {ι : Type*} [Finite ι] (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ r i := by
  classical
  let _ := Fintype.ofFinite ι
  have aux (s : Finset ι) : ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ ≤ r i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨δ, hδ, h⟩ := ih
      refine ⟨min δ (r a), lt_min hδ (hr a), ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (h i hi)
  obtain ⟨δ, hδ, h⟩ := aux Finset.univ
  exact ⟨δ, hδ, fun i => h i (Finset.mem_univ i)⟩

theorem uniform_thickening {ι : Type*} [Finite ι] (K : ι → Set (ℝ × ℝ))
    (hK : ∀ i, IsCompact (K i)) (R : ι → ι → Prop)
    (hR : ∀ i j, R i j → Disjoint (K i) (K j)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i j, R i j →
      Disjoint (Metric.thickening δ (K i)) (Metric.thickening δ (K j)) := by
  classical
  let I := {p : ι × ι // R p.1 p.2}
  have hex (p : I) : ∃ δ : ℝ, 0 < δ ∧
      Disjoint (Metric.thickening δ (K p.val.1)) (Metric.thickening δ (K p.val.2)) :=
    (hR _ _ p.property).exists_thickenings (hK _) (hK _).isClosed
  choose r hr hd using hex
  obtain ⟨δ, hδ, hle⟩ := finite_positive_radius r hr
  refine ⟨δ, hδ, ?_⟩
  intro i j hij
  let p : I := ⟨(i, j), hij⟩
  exact (hd p).mono (Metric.thickening_mono (hle p) _) (Metric.thickening_mono (hle p) _)

end
end Barnette.PlaneEmbedding

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.PlaneEmbedding


theorem solution : type_of% @_root_.OAI.Barnette.PlaneEmbedding.uniform_thickening := @_root_.OAI.Barnette.PlaneEmbedding.uniform_thickening
