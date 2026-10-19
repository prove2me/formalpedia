-- Prove2me | solution 1 for OAI.Barnette.cycleCoordinates_of_not_acyclic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:02:58.89148+00:00
-- url     : https://prove2.me/submissions/070fc6a5-1221-45e6-ba9f-a342d9e521a8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/CycleReversal.lean:L17-L32
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.cycleCoordinates_of_not_acyclic. The node keeps its source
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

-- ---- from OAI.Combinatorics.Hamiltonian.CycleReversal ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Reversal involutions on partners of a fixed incidence state. -/

namespace Barnette

open Fin.NatCast

variable {V : Type*} {G : SimpleGraph V}

theorem cycleCoordinates_of_not_acyclic (hG : ¬G.IsAcyclic) :
    Nonempty (CycleCoordinates G) := by
  classical
  simp only [SimpleGraph.IsAcyclic, not_forall, not_not] at hG
  obtain ⟨v, p, hp⟩ := hG
  have hlen : 3 ≤ p.length := hp.isCircuit.three_le_length
  obtain ⟨f⟩ := (SimpleGraph.cycleGraph_isContained_iff (show 2 < p.length by omega)).mpr
    ⟨v, p, hp, rfl⟩
  have heq : p.length = (p.length - 3) + 3 := by omega
  rw [heq] at f
  refine ⟨⟨p.length - 3, ⟨f.toHom, f.injective⟩, ?_⟩⟩
  intro i
  apply f.toHom.map_adj
  apply SimpleGraph.cycleGraph_adj'.mpr
  right
  simp

namespace TriangleSystem

variable {A : Type*} (T : TriangleSystem A V) {X : Set V}

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
open OAI OAI.Barnette
open Fin.NatCast


theorem solution : type_of% @_root_.OAI.Barnette.cycleCoordinates_of_not_acyclic := @_root_.OAI.Barnette.cycleCoordinates_of_not_acyclic
