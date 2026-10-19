-- Prove2me | solution 1 for OAI.Barnette.TriangleSystem.oppositeCycle_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:04:53.397262+00:00
-- url     : https://prove2.me/submissions/c3e20cb4-5fd4-4058-ada1-4e396168eda5

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/CycleReversal.lean:L52-L78
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.TriangleSystem.oppositeCycle_nonempty. The node keeps its source
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

end
end Barnette.Network

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.CycleReversal ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Reversal involutions on partners of a fixed incidence state. -/

namespace Barnette

open Fin.NatCast

variable {V : Type*} {G : SimpleGraph V}

namespace TriangleSystem

variable {A : Type*} (T : TriangleSystem A V) {X : Set V}

theorem opposite_indices : ∀ i j k l s : Fin 3,
    i ≠ j → k ≠ l → i ≠ s → j ≠ s → k ≠ s → l ≠ s →
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by decide

theorem oppositeCycle_nonempty (s : T.State X) (hc : ¬(T.oppositeGraph s).IsAcyclic) :
    Nonempty (T.OppositeCycle s) := by
  classical
  obtain ⟨C⟩ := cycleCoordinates_of_not_acyclic hc
  choose face l r hl hr hls hrs using fun i => (C.adjacent i).2
  have hlr (i) : l i ≠ r i := by
    intro h
    have hh : C.vertex i = C.vertex (i + 1) := (hl i).symm.trans (h ▸ hr i)
    have heq := C.vertex.injective hh
    apply cyclic_one_ne_zero C.n
    exact add_left_cancel (by simpa using heq.symm : i + 1 = i + 0)
  have hface : Function.Injective face := by
    intro i j hij
    have hls' := hls j
    have hrs' := hrs j
    rw [← hij] at hls' hrs'
    have h := opposite_indices (l i) (r i) (l j) (r j) (s.val (face i))
      (hlr i) (hlr j) (hls i) (hrs i) hls' hrs'
    apply C.edge_indices_unique i j
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · left
      exact ⟨(hl i).symm.trans (by rw [hij, h₁, hl]),
        (hr i).symm.trans (by rw [hij, h₂, hr])⟩
    · right
      exact ⟨(hl i).symm.trans (by rw [hij, h₁, hr]),
        (hr i).symm.trans (by rw [hij, h₂, hl])⟩
  exact ⟨⟨C, ⟨face, hface⟩, l, r, hl, hr, hls, hrs⟩⟩

namespace OppositeCycle

variable {T} {s r : T.State X} (C : T.OppositeCycle s)

end OppositeCycle
end TriangleSystem
end Barnette

namespace Barnette.TriangleSystem

open Fin.NatCast

variable {A V : Type*} {T : TriangleSystem A V} {X : Set V} {s : T.State X}

namespace OppositeCycle

variable (C : T.OppositeCycle s)

end OppositeCycle

namespace OppositeCycle

variable (C : T.OppositeCycle s)

end OppositeCycle
end Barnette.TriangleSystem

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.TriangleSystem
open Fin.NatCast


theorem solution : type_of% @_root_.OAI.Barnette.TriangleSystem.oppositeCycle_nonempty := @_root_.OAI.Barnette.TriangleSystem.oppositeCycle_nonempty
