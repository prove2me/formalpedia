-- Prove2me | solution 1 for OAI.Barnette.PlaneEmbedding.exists_lattice_corridor_model
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T05:17:16.399331+00:00
-- url     : https://prove2.me/submissions/735b6b09-621b-45cb-af27-129e1f0e63d2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Corridors.lean:L58-L90
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.PlaneEmbedding.exists_lattice_corridor_model. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Corridors
import Theorems.Thm_OAI_Barnette_PlaneEmbedding_branch_core_disjoint
import Theorems.Thm_OAI_Barnette_PlaneEmbedding_branch_disjoint
import Theorems.Thm_OAI_Barnette_PlaneEmbedding_uniform_thickening
import Theorems.Thm_OAI_Barnette_SquareGrid_cell_cover
import Theorems.Thm_OAI_Barnette_SquareGrid_cells_connected
import Theorems.Thm_OAI_Barnette_SquareGrid_cells_finite

-- ---- from OAI.Combinatorics.Hamiltonian.Traces ----
namespace OAI

/-! Compact connected arc traces and uniform positive thickenings. -/

namespace Barnette.PlaneEmbedding

noncomputable section

variable {V : Type*} {G : SimpleGraph V} (E : PlaneEmbedding G)

theorem curve_symm (d : G.Dart) (t : unitInterval) :
    E.curve d.symm t = E.curve d (unitInterval.symm t) := by
  change E.arc d.snd d.fst d.adj.symm t = _
  rw [E.arc_reverse]
  rfl

theorem curve_eq_curve_interior {d e : G.Dart} {t s : unitInterval}
    (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) (hs₀ : s ≠ 0) (hs₁ : s ≠ 1)
    (h : E.curve d t = E.curve e s) : d = e ∨ d = e.symm := by
  rcases E.interiors_disjoint d.fst d.snd e.fst e.snd d.adj e.adj
    t s ht₀ ht₁ hs₀ hs₁ h with h | h
  · exact Or.inl (SimpleGraph.Dart.ext _ _ (Prod.ext h.1 h.2))
  · exact Or.inr (SimpleGraph.Dart.ext _ _ (Prod.ext h.1 h.2))

theorem trace_compact (d : G.Dart) (a b : unitInterval) :
    IsCompact (E.trace d a b) :=
  isCompact_Icc.image (E.curve d).continuous

theorem trace_preconnected (d : G.Dart) (a b : unitInterval) :
    IsPreconnected (E.trace d a b) :=
  isPreconnected_Icc.image _ (E.curve d).continuous.continuousOn

theorem branch_point (v : V) : E.point v ∈ E.branch v :=
  Or.inl rfl

theorem branch_compact [Finite V] (v : V) : IsCompact (E.branch v) := by
  classical
  have : Finite G.Dart := Finite.of_injective SimpleGraph.Dart.toProd
    SimpleGraph.Dart.toProd_injective
  exact isCompact_singleton.union (isCompact_iUnion fun d => E.trace_compact d.val 0 third)

theorem core_compact (d : G.Dart) : IsCompact (E.core d) := E.trace_compact _ _ _

theorem core_preconnected (d : G.Dart) : IsPreconnected (E.core d) :=
  E.trace_preconnected _ _ _

private theorem middle_nonendpoint {t : unitInterval} (ht : t ∈ Set.Icc third twoThirds) :
    t ≠ 0 ∧ t ≠ 1 := by
  constructor
  · intro h
    have hh : (1 : ℝ) / 3 ≤ t := ht.1
    rw [h] at hh
    norm_num at hh
  · intro h
    have hh : (t : ℝ) ≤ 2 / 3 := ht.2
    rw [h] at hh
    norm_num at hh

theorem core_disjoint {d e : G.Dart} (hde : d.edge ≠ e.edge) :
    Disjoint (E.core d) (E.core e) := by
  rw [Set.disjoint_left]
  rintro p ⟨t, ht, heq⟩ ⟨s, hs, heq'⟩
  obtain ⟨ht₀, ht₁⟩ := middle_nonendpoint ht
  obtain ⟨hs₀, hs₁⟩ := middle_nonendpoint hs
  rcases E.curve_eq_curve_interior ht₀ ht₁ hs₀ hs₁ (heq.trans heq'.symm) with h | h
  · exact hde (congrArg SimpleGraph.Dart.edge h)
  · exact hde ((congrArg SimpleGraph.Dart.edge h).trans e.edge_symm)

theorem branch_preconnected (v : V) : IsPreconnected (E.branch v) := by
  apply isPreconnected_of_forall (E.point v)
  intro y hy
  rcases hy with hy | hy
  · exact ⟨{E.point v}, Set.subset_union_left, rfl, hy, isPreconnected_singleton⟩
  · obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hy
    refine ⟨E.trace d.val 0 third, ?_, ?_, hd, E.trace_preconnected _ _ _⟩
    · exact fun x hx => Or.inr (Set.mem_iUnion.mpr ⟨d, hx⟩)
    · refine ⟨0, ⟨le_rfl, ?_⟩, ?_⟩
      · change (0 : ℝ) ≤ 1 / 3
        norm_num
      · simpa only [E.curve_zero] using congrArg E.point d.property

theorem branch_connected (v : V) : IsConnected (E.branch v) :=
  ⟨⟨_, E.branch_point v⟩, E.branch_preconnected v⟩

private theorem third_le_twoThirds : third ≤ twoThirds := by
  change (1 : ℝ) / 3 ≤ 2 / 3
  norm_num

private theorem symm_third : unitInterval.symm third = twoThirds := by
  apply Subtype.ext
  change 1 - (1 : ℝ) / 3 = 2 / 3
  norm_num

theorem core_connected (d : G.Dart) : IsConnected (E.core d) :=
  ⟨⟨E.curve d third, third, ⟨le_rfl, third_le_twoThirds⟩, rfl⟩,
    E.core_preconnected d⟩

theorem branch_core_meets (d : G.Dart) :
    (E.branch d.fst ∩ E.core d).Nonempty ∧ (E.branch d.snd ∩ E.core d).Nonempty := by
  constructor
  · refine ⟨E.curve d third, ?_, third, ⟨le_rfl, third_le_twoThirds⟩, rfl⟩
    refine Or.inr (Set.mem_iUnion.mpr ⟨⟨d, rfl⟩, third, ⟨?_, le_rfl⟩, rfl⟩)
    change (0 : ℝ) ≤ 1 / 3
    norm_num
  · refine ⟨E.curve d twoThirds, ?_, twoThirds, ⟨third_le_twoThirds, le_rfl⟩, rfl⟩
    refine Or.inr (Set.mem_iUnion.mpr ⟨⟨d.symm, rfl⟩, third, ⟨?_, le_rfl⟩, ?_⟩)
    · change (0 : ℝ) ≤ 1 / 3
      norm_num
    · rw [E.curve_symm, symm_third]

end
end Barnette.PlaneEmbedding

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.SquareGrid ----
namespace OAI

/-! Ordinary square cells and connected finite lattice corridors. -/

namespace Barnette.SquareGrid

noncomputable section

theorem dist_le_of_mem_cell {δ : ℝ} {z : ℤ × ℤ} {p q : ℝ × ℝ}
    (hp : p ∈ cell δ z) (hq : q ∈ cell δ z) : dist p q ≤ δ := by
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq]
  constructor <;> rw [abs_le] <;> constructor <;>
    nlinarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2, hq.1.1, hq.1.2, hq.2.1, hq.2.2]

theorem cell_subset_thickening {δ ε : ℝ} (hδε : δ < ε) {K : Set (ℝ × ℝ)}
    {z : ℤ × ℤ} (hz : z ∈ cells δ K) : cell δ z ⊆ Metric.thickening ε K := by
  obtain ⟨q, hq, hqK⟩ := hz
  intro p hp
  exact Metric.mem_thickening_iff.mpr ⟨q, hqK, (dist_le_of_mem_cell hp hq).trans_lt hδε⟩

theorem cells_disjoint {δ ε : ℝ} (hδε : δ < ε)
    {K L : Set (ℝ × ℝ)}
    (hKL : Disjoint (Metric.thickening ε K) (Metric.thickening ε L)) :
    Disjoint (cells δ K) (cells δ L) := by
  rw [Set.disjoint_left] at hKL ⊢
  intro z hz hz'
  have hzp := hz
  obtain ⟨p, hp, _⟩ := hzp
  exact hKL (cell_subset_thickening hδε hz hp) (cell_subset_thickening hδε hz' hp)

end
end Barnette.SquareGrid
namespace Barnette.SquareGrid

noncomputable section

end
end Barnette.SquareGrid

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.Corridors ----
namespace OAI

/-! Disjoint lattice corridors obtained from a crossing-free plane embedding. -/

namespace Barnette

namespace PlaneEmbedding

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj] (E : PlaneEmbedding G)

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem allSets_compact (i : V ⊕ G.Dart) : IsCompact (E.allSets i) := by
  cases i with
  | inl v => exact E.branch_compact v
  | inr d => exact E.core_compact d

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem allSets_disjoint (i j : V ⊕ G.Dart) (h : apart i j) :
    Disjoint (E.allSets i) (E.allSets j) := by
  cases i with
  | inl v =>
    cases j with
    | inl w => exact E.branch_disjoint h
    | inr d => exact E.branch_core_disjoint h.1 h.2
  | inr d =>
    cases j with
    | inl v => exact (E.branch_core_disjoint h.1 h.2).symm
    | inr e => exact E.core_disjoint h

omit [DecidableEq V] in
include E in

theorem exists_lattice_corridor_model : Nonempty (CorridorModel G SquareGrid.graph) := by
  classical
  obtain ⟨ε, hε, hsep⟩ := uniform_thickening E.allSets E.allSets_compact apart E.allSets_disjoint
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := half_pos hε
  have hδε : δ < ε := half_lt_self hε
  have hdis (i j : V ⊕ G.Dart) (h : apart i j) :
      Disjoint (SquareGrid.cells δ (E.allSets i)) (SquareGrid.cells δ (E.allSets j)) :=
    SquareGrid.cells_disjoint hδε (hsep i j h)
  refine ⟨{
    branch := fun v => SquareGrid.cells δ (E.branch v)
    corridor := fun d => SquareGrid.cells δ (E.core d)
    branch_finite := fun v => SquareGrid.cells_finite hδ (E.branch_compact v)
    corridor_finite := fun d => SquareGrid.cells_finite hδ (E.core_compact d)
    branch_connected := fun v => SquareGrid.cells_connected hδ (E.branch_compact v)
      (E.branch_connected v)
    corridor_connected := fun d => SquareGrid.cells_connected hδ (E.core_compact d)
      (E.core_connected d)
    branches_disjoint := fun v w h => hdis (.inl v) (.inl w) h
    corridors_disjoint := fun d e h => hdis (.inr d) (.inr e) h
    nonincident_disjoint := fun v d h₁ h₂ => hdis (.inl v) (.inr d) ⟨h₁, h₂⟩
    incident_meets := ?_
  }⟩
  intro d
  have meets {K L : Set (ℝ × ℝ)} (h : (K ∩ L).Nonempty) :
      (SquareGrid.cells δ K ∩ SquareGrid.cells δ L).Nonempty := by
    obtain ⟨p, hpK, hpL⟩ := h
    obtain ⟨z, hz⟩ := SquareGrid.cell_cover hδ p
    exact ⟨z, ⟨p, hz, hpK⟩, ⟨p, hz, hpL⟩⟩
  exact ⟨meets (E.branch_core_meets d).1, meets (E.branch_core_meets d).2⟩

end
end PlaneEmbedding
end Barnette

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.PlaneEmbedding


theorem solution : type_of% @_root_.OAI.Barnette.PlaneEmbedding.exists_lattice_corridor_model := @_root_.OAI.Barnette.PlaneEmbedding.exists_lattice_corridor_model
