-- Prove2me | solution 1 for OAI.Barnette.Network.nontrivial_threeCut
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:57:48.426813+00:00
-- url     : https://prove2.me/submissions/7fff7f05-6b2c-46e5-90dd-843d89594fc3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/CappedDuality.lean:L167-L179
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.nontrivial_threeCut. The node keeps its source
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

-- ---- from OAI.Combinatorics.Hamiltonian.CappedDuality ----
namespace OAI

/-! Exact duals of capped graphs and Hamiltonian walks in degree-two graphs. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
universe uF
variable {V E W K : Type*} {F : Type uF} [Fintype V] [Fintype E] [Fintype F]
  [Fintype W] [Fintype K]

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
universe uF
variable {V E : Type*} {F : Type uF} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

lemma nontrivial_threeCut (h : ¬N.TrivialThreeCuts) :
    ∃ A : Finset V, (N.cut A).card = 3 ∧ 2 ≤ A.card ∧ 2 ≤ Aᶜ.card := by
  unfold TrivialThreeCuts at h
  push Not at h
  obtain ⟨A,hcut,ha,ho⟩ := h
  have he : (N.cut A).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨e,he⟩ := he
  have hh := (N.mem_cut A e).mp he
  have hi : A.Nonempty := hh.elim (fun h => ⟨_,h.1⟩) (fun h => ⟨_,h.1⟩)
  have hout : Aᶜ.Nonempty := hh.elim (fun h => ⟨_,Finset.mem_compl.mpr h.2⟩) (fun h => ⟨_,Finset.mem_compl.mpr h.2⟩)
  have hi' := Finset.card_pos.mpr hi
  have ho' := Finset.card_pos.mpr hout
  exact ⟨A,hcut,by omega,by omega⟩
end
end Barnette.Network
namespace Barnette.SimpleCycle
noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

end
end Barnette.SimpleCycle

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.nontrivial_threeCut := @_root_.OAI.Barnette.Network.nontrivial_threeCut
