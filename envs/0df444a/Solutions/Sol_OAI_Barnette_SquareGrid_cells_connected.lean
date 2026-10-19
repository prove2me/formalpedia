-- Prove2me | solution 1 for OAI.Barnette.SquareGrid.cells_connected
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T05:15:03.837073+00:00
-- url     : https://prove2.me/submissions/d358ede8-8531-418e-bb5e-58440957d41b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/SquareGrid.lean:L169-L184
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.SquareGrid.cells_connected. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_Hamiltonian_SquareGrid
import Theorems.Thm_OAI_Barnette_SquareGrid_cell_cover
import Theorems.Thm_OAI_Barnette_SquareGrid_cells_finite

-- ---- from OAI.Combinatorics.Hamiltonian.SquareGrid ----
namespace OAI

/-! Ordinary square cells and connected finite lattice corridors. -/

namespace Barnette.SquareGrid

noncomputable section

theorem cell_closed (δ : ℝ) (z : ℤ × ℤ) : IsClosed (cell δ z) :=
  isClosed_Icc.prod isClosed_Icc

theorem subset_union_cells {δ : ℝ} (hδ : 0 < δ) (K : Set (ℝ × ℝ)) :
    K ⊆ ⋃ z : cells δ K, cell δ z.val := by
  intro p hp
  obtain ⟨z, hz⟩ := cell_cover hδ p
  exact Set.mem_iUnion.mpr ⟨⟨z, p, hz, hp⟩, hz⟩

end
end Barnette.SquareGrid
namespace Barnette.SquareGrid

noncomputable section

theorem finite_closed_cover_preconnected {ι α : Type*} [Finite ι] [TopologicalSpace α]
    (H : SimpleGraph ι) (K : Set α) (C : ι → Set α)
    (hK : IsPreconnected K) (hC : ∀ i, IsClosed (C i))
    (hcover : K ⊆ ⋃ i, C i) (hne : ∀ i, (K ∩ C i).Nonempty)
    (hjoin : ∀ p ∈ K, ∀ i j, p ∈ C i → p ∈ C j → H.Reachable i j) :
    H.Preconnected := by
  classical
  intro a b
  by_contra hab
  let U : Set α := ⋃ i : {i // H.Reachable a i}, C i.val
  let W : Set α := ⋃ i : {i // ¬H.Reachable a i}, C i.val
  have hU : IsClosed U := isClosed_iUnion_of_finite (fun i => hC i.val)
  have hW : IsClosed W := isClosed_iUnion_of_finite (fun i => hC i.val)
  have hUW : K ⊆ U ∪ W := by
    intro p hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hp)
    by_cases hai : H.Reachable a i
    · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨i, hai⟩, hi⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i, hai⟩, hi⟩)
  have haU : (K ∩ U).Nonempty := by
    obtain ⟨p, hpK, hpa⟩ := hne a
    exact ⟨p, hpK, Set.mem_iUnion.mpr ⟨⟨a, .rfl⟩, hpa⟩⟩
  have hbW : (K ∩ W).Nonempty := by
    obtain ⟨p, hpK, hpb⟩ := hne b
    exact ⟨p, hpK, Set.mem_iUnion.mpr ⟨⟨b, hab⟩, hpb⟩⟩
  obtain ⟨p, hpK, hpU, hpW⟩ :=
    isPreconnected_closed_iff.mp hK U W hU hW hUW haU hbW
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpU
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hpW
  exact j.property (i.property.trans (hjoin p hpK i.val j.val hi hj))

private theorem coordinates_close {δ : ℝ} (hδ : 0 < δ) {a b : ℤ} {p : ℝ}
    (ha : δ * a ≤ p ∧ p ≤ δ * ((a : ℝ) + 1))
    (hb : δ * b ≤ p ∧ p ≤ δ * ((b : ℝ) + 1)) :
    a ≤ b + 1 ∧ b ≤ a + 1 := by
  have hab : (a : ℝ) ≤ (b : ℝ) + 1 := (mul_le_mul_iff_right₀ hδ).mp (ha.1.trans hb.2)
  have hba : (b : ℝ) ≤ (a : ℝ) + 1 := (mul_le_mul_iff_right₀ hδ).mp (hb.1.trans ha.2)
  exact ⟨by exact_mod_cast hab, by exact_mod_cast hba⟩

theorem reachable_of_common_point {δ : ℝ} (hδ : 0 < δ) {K : Set (ℝ × ℝ)}
    {p : ℝ × ℝ} (hp : p ∈ K) (a b : cells δ K)
    (ha : p ∈ cell δ a.val) (hb : p ∈ cell δ b.val) :
    (graph.induce (cells δ K)).Reachable a b := by
  obtain ⟨hx, hx'⟩ := coordinates_close hδ ha.1 hb.1
  obtain ⟨hy, hy'⟩ := coordinates_close hδ ha.2 hb.2
  let c : cells δ K := ⟨(b.val.1, a.val.2), p, ⟨hb.1, ha.2⟩, hp⟩
  have hac : (graph.induce (cells δ K)).Reachable a c := by
    by_cases h : a.val.1 = b.val.1
    · have heq : a = c := Subtype.ext (Prod.ext h rfl)
      rw [← heq]
    · apply SimpleGraph.Adj.reachable
      change graph.Adj a.val c.val
      exact Or.inl ⟨by dsimp [c]; omega, rfl⟩
  have hcb : (graph.induce (cells δ K)).Reachable c b := by
    by_cases h : a.val.2 = b.val.2
    · have heq : c = b := Subtype.ext (Prod.ext rfl h)
      rw [heq]
    · apply SimpleGraph.Adj.reachable
      change graph.Adj c.val b.val
      exact Or.inr ⟨by dsimp [c]; omega, rfl⟩
  exact hac.trans hcb

theorem cells_connected {δ : ℝ} (hδ : 0 < δ) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hc : IsConnected K) :
    (graph.induce (cells δ K)).Connected := by
  classical
  let _ : Fintype (cells δ K) := (cells_finite hδ hK).fintype
  have hone : Nonempty (cells δ K) := by
    obtain ⟨p, hp⟩ := hc.nonempty
    obtain ⟨z, hz⟩ := cell_cover hδ p
    exact ⟨⟨z, p, hz, hp⟩⟩
  refine ⟨finite_closed_cover_preconnected _ K (fun z : cells δ K => cell δ z.val)
    hc.isPreconnected (fun z => cell_closed _ _) (subset_union_cells hδ K) ?_ ?_⟩
  · intro z
    obtain ⟨p, hp, hpK⟩ := z.property
    exact ⟨p, hpK, hp⟩
  · intro p hp a b ha hb
    exact reachable_of_common_point hδ hp a b ha hb

end
end Barnette.SquareGrid

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.SquareGrid


theorem solution : type_of% @_root_.OAI.Barnette.SquareGrid.cells_connected := @_root_.OAI.Barnette.SquareGrid.cells_connected
