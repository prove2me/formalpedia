-- Prove2me | solution 1 for OAI.Barnette.Network.cap_connectedFibers
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:50:00.200366+00:00
-- url     : https://prove2.me/submissions/68b2286d-03a8-41dc-975b-3c0bb1a10679

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/ThreeCuts.lean:L274-L296
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.cap_connectedFibers. The node keeps its source
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

-- ---- from OAI.Combinatorics.Hamiltonian.ThreeCuts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Three-edge cuts, capped graphs, and preservation of graph properties. -/

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
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] [Fintype E] in
lemma cap_connectedFibers (A : Finset V)
    (hc : (N.graph.induce {v | v ∉ A}).Connected) : N.ConnectedFibers (N.capMap A) := by
  intro v w he
  by_cases hv : v ∈ A
  · have hv' := N.capMap_some A ⟨v,hv⟩
    rw [hv'] at he
    have hh : w = v := (N.capMap_eq_some A _ _).mp he.symm
    subst w
    exact SimpleGraph.Reachable.refl v
  · have hw : w ∉ A := (N.capMap_eq_none A w).mp (he.symm.trans ((N.capMap_eq_none A v).mpr hv))
    let f : (N.graph.induce {v | v ∉ A}) →g (N.restrict (Subtype.val : N.internal (N.capMap A) → E)).graph := {
      toFun := Subtype.val
      map_rel' := by
        intro x y hxy
        obtain ⟨hne,e,hee⟩ := hxy
        change (N.tail e = x.val ∧ N.head e = y.val) ∨ (N.tail e = y.val ∧ N.head e = x.val) at hee
        have hm : e ∈ N.internal (N.capMap A) := by
          rcases hee with ⟨ht,hh⟩|⟨ht,hh⟩ <;>
            change N.capMap A (N.tail e) = N.capMap A (N.head e) <;>
            rw [ht,hh,(N.capMap_eq_none A _).mpr x.property,(N.capMap_eq_none A _).mpr y.property]
        exact ⟨hne,⟨e,hm⟩,hee⟩ }
    exact (hc ⟨v,hv⟩ ⟨w,hw⟩).map f
end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

variable {F : Type*} [Fintype F] (D : Network F E)

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.cap_connectedFibers := @_root_.OAI.Barnette.Network.cap_connectedFibers
