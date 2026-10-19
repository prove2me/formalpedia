-- Prove2me | solution 1 for OAI.Barnette.Network.addSink_acyclic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:31:39.5916+00:00
-- url     : https://prove2.me/submissions/1cc4665a-71c2-4f4f-8b5f-79b4a24a0c64

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Matching.lean:L119-L154
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.addSink_acyclic. The node keeps its source
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
import Theorems.Thm_OAI_Barnette_cycleCoordinates_of_not_acyclic

-- ---- from OAI.Combinatorics.Hamiltonian.FlowCircuits ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Minimal flow circuits, triangular faces, and simple cycle coordinates. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

end
end Barnette.Network
namespace Barnette

open Fin.NatCast

theorem cyclic_two_ne_zero (n : ℕ) : (2 : Fin (n + 3)) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp [Nat.mod_eq_of_lt (show 2 < n + 3 by omega)] at this

namespace CycleCoordinates

variable {V : Type*} {G : SimpleGraph V} (C : CycleCoordinates G)

theorem edge_indices_unique (i j : Fin (C.n + 3))
    (h : (C.vertex i = C.vertex j ∧ C.vertex (i + 1) = C.vertex (j + 1)) ∨
      (C.vertex i = C.vertex (j + 1) ∧ C.vertex (i + 1) = C.vertex j)) : i = j := by
  rcases h with h | h
  · exact C.vertex.injective h.1
  · have hi := C.vertex.injective h.1
    have hj := C.vertex.injective h.2
    have hh : (2 : Fin (C.n + 3)) = 0 := by
      have : j + (1 + 1) = j + 0 := by simpa [hi, add_assoc] using hj
      simpa only [show (1 : Fin (C.n + 3)) + 1 = 2 by
        apply Fin.ext
        simp [Fin.val_add, Nat.mod_eq_of_lt (show 2 < C.n + 3 by omega)]] using (add_left_cancel this)
    exact (cyclic_two_ne_zero C.n hh).elim

end CycleCoordinates
end Barnette

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E]
  (N : Network V E) (C : Barnette.CycleCoordinates N.graph)

omit [Fintype V] [Fintype E] in
lemma cycleEdge_ends (i : Fin (C.n+3)) :
    s(N.tail (N.cycleEdge C i),N.head (N.cycleEdge C i)) = s(C.vertex i,C.vertex (i+1)) :=
  Sym2.eq_iff.mpr (C.adjacent i).2.choose_spec

omit [Fintype V] [Fintype E] in
lemma cycleEdge_injective : Function.Injective (N.cycleEdge C) := by
  intro i j hij
  apply C.edge_indices_unique i j
  apply Sym2.eq_iff.mp
  rw [← N.cycleEdge_ends C i, ← N.cycleEdge_ends C j, hij]

end
end Barnette.Network

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.Matching ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Disk and spoke signs and matching complements. -/

namespace Barnette.CycleCoordinates
variable {V : Type*} {G : SimpleGraph V} (C : Barnette.CycleCoordinates G)
include C in
lemma not_acyclic : ¬ G.IsAcyclic := by
  intro ha
  apply (SimpleGraph.isAcyclic_iff_free_cycleGraph.mp ha) (C.n+3) (by omega)
  refine ⟨⟨⟨C.vertex,?_⟩,C.vertex.injective⟩⟩
  intro i j hij
  rcases SimpleGraph.cycleGraph_adj.mp hij with hij | hij
  · have hi : i = j+1 := (sub_eq_iff_eq_add.mp hij).trans (add_comm _ _)
    rw [hi]; exact (C.adjacent j).symm
  · have hj : j = i+1 := (sub_eq_iff_eq_add.mp hij).trans (add_comm _ _)
    rw [hj]; exact C.adjacent i
end Barnette.CycleCoordinates

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

variable {F : Type*} [Fintype F] (D : Network F E)
end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V A : Type*} (Q : Network V A)

lemma addSink_tail_injective (ht : Function.Injective Q.tail) (r : Fin 2 → V)
    (hr : Function.Injective r) (hd : ∀ a i, Q.tail a ≠ r i) (z : V) :
    Function.Injective (Q.addSink r z).tail := by
  rintro (a|i) (b|j) h
  · exact congrArg Sum.inl (ht h)
  · exact (hd a j h).elim
  · exact (hd b i h.symm).elim
  · exact congrArg Sum.inr (hr h)

lemma addSink_acyclic (ha : Q.graph.IsAcyclic) (ht : Function.Injective Q.tail)
    (r : Fin 2 → V) (hr : Function.Injective r) (hd : ∀ a i, Q.tail a ≠ r i)
    (z : V) (hz : z ∉ Set.range (Q.addSink r z).tail) : (Q.addSink r z).graph.IsAcyclic := by
  classical
  by_contra hnot
  obtain ⟨C⟩ := Barnette.cycleCoordinates_of_not_acyclic hnot
  let L := Q.addSink r z
  let edge : Fin (C.n+3) ↪ A ⊕ Fin 2 := ⟨L.cycleEdge C,L.cycleEdge_injective C⟩
  have hend (i) : L.tail (edge i) = C.vertex i ∨ L.tail (edge i) = C.vertex (i+1) := by
    rcases Sym2.eq_iff.mp (L.cycleEdge_ends C i) with h|h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hor := C.tail_orientation edge L.tail (Q.addSink_tail_injective ht r hr hd z) hend
  have hrange (i) : C.vertex i ∈ Set.range L.tail := by
    rcases hor with hf|hb
    · exact ⟨edge i,hf i⟩
    · refine ⟨edge (i-1),?_⟩
      simpa using hb (i-1)
  have hbase (i) : ∃ a, edge i = Sum.inl a := by
    cases he : edge i with
    | inl a => exact ⟨a,rfl⟩
    | inr j =>
      have hh : L.head (edge i) = z := by rw [he]; rfl
      rcases Sym2.eq_iff.mp (L.cycleEdge_ends C i) with h|h
      · exact (hz (hh ▸ (h.2 ▸ hrange (i+1)))).elim
      · exact (hz (hh ▸ (h.2 ▸ hrange i))).elim
  have hc : Nonempty (Barnette.CycleCoordinates Q.graph) := by
    refine ⟨⟨C.n,C.vertex,?_⟩⟩
    intro i
    obtain ⟨a,hea⟩ := hbase i
    refine ⟨(C.adjacent i).1,a,?_⟩
    have he := L.cycleEdge_ends C i
    change s(L.tail (edge i),L.head (edge i)) = _ at he
    rw [hea] at he
    exact Sym2.eq_iff.mp he
  exact hc.elim (fun C' => C'.not_acyclic ha)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

end
end Barnette.Network
namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
open Barnette.TriangleSystem
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

end
end Barnette.Network.ColoredDual
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} (D : Network V E)

end
end Barnette.Network

namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
open Barnette.TriangleSystem
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

end
end Barnette.Network.ColoredDual

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.addSink_acyclic := @_root_.OAI.Barnette.Network.addSink_acyclic
