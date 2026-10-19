-- Prove2me | solution 1 for OAI.Barnette.TriangleSystem.oppositeGraph_adj_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:55:14.466826+00:00
-- url     : https://prove2.me/submissions/9d5b35aa-f2d5-4f71-aec1-34506a222ad6

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/TriangleSystem.lean:L117-L138
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.TriangleSystem.oppositeGraph_adj_iff. The node keeps its source
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

-- ---- from OAI.Combinatorics.Hamiltonian.TriangleSystem ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Triangle incidence states, opposite graphs, and oriented potentials. -/

namespace Barnette

namespace TriangleSystem

variable {A V : Type*} (T : TriangleSystem A V)

namespace State

variable {T} {X : Set V}

end State

theorem oppositeGraph_adj_iff {X : Set V} {r s : T.State X} (hrs : T.Partner r s)
    (v w : V) : (T.oppositeGraph s).Adj v w ↔
    ∃ t, (v = r.value t ∧ w = T.vertex t (thirdIndex (r.val t) (s.val t))) ∨
      (w = r.value t ∧ v = T.vertex t (thirdIndex (r.val t) (s.val t))) := by
  constructor
  · rintro ⟨hvw, t, i, j, hi, hj, his, hjs⟩
    have hij : i ≠ j := fun h => hvw (hi.symm.trans (h ▸ hj))
    have hrs' : r.val t ≠ s.val t := fun h => hrs t ((State.value_eq_iff r s t).mpr h)
    refine ⟨t, ?_⟩
    rcases other_corners i j (r.val t) (s.val t) hij his hjs hrs' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hi.symm, hj.symm⟩
    · exact Or.inr ⟨hj.symm, hi.symm⟩
  · rintro ⟨t, h | h⟩
    all_goals
      have hrs' : r.val t ≠ s.val t := fun h => hrs t ((State.value_eq_iff r s t).mpr h)
      have hne := thirdIndex_distinct (r.val t) (s.val t) hrs'
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨fun heq => hne.1 (T.vertex_injective t heq.symm),
        t, r.val t, thirdIndex (r.val t) (s.val t), rfl, rfl, hrs', hne.2⟩
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨fun heq => hne.1 (T.vertex_injective t heq),
        t, thirdIndex (r.val t) (s.val t), r.val t, rfl, rfl, hne.2, hrs'⟩

end TriangleSystem
end Barnette
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.TriangleSystem


theorem solution : type_of% @_root_.OAI.Barnette.TriangleSystem.oppositeGraph_adj_iff := @_root_.OAI.Barnette.TriangleSystem.oppositeGraph_adj_iff
