-- Prove2me | solution 1 for OAI.Barnette.Network.Triangle.corner_iff_incident
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:31:27.704442+00:00
-- url     : https://prove2.me/submissions/bf92d3b0-6a62-4232-9ec9-c70644c99a9e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Bonds.lean:L217-L232
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.Triangle.corner_iff_incident. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds

-- ---- from OAI.Combinatorics.Hamiltonian.CutSpaces ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Cuts, simplicity, and connectivity of finite oriented networks. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} (N : Network V E)

variable [Fintype V] [Fintype E]
variable {F : Type*} [Fintype F] (D : Network F E)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] [Fintype E] in
lemma incident_iff_mem_pair (e : E) (v : V) :
    N.Incident e v ↔ v ∈ s(N.tail e, N.head e) := by
  simp only [Incident, Sym2.mem_iff]
  tauto

end
end Barnette.Network

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.Bonds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Cycle flows, minimal cuts, and connected shores. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E]
  (N : Network V E) (C : Barnette.CycleCoordinates N.graph)

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
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype E] [Fintype F] in
lemma Triangle.corner_iff_incident {s : Finset E} (t : D.Triangle s) (v : F) :
    v ∈ Set.range t.corner ↔ ∃ e ∈ s, D.Incident e v := by
  constructor
  · rintro ⟨i,rfl⟩
    refine ⟨t.edge i,?_,?_⟩
    · have hm : t.edge i ∈ Finset.univ.image t.edge := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
      rwa [t.edge_range] at hm
    · rw [D.incident_iff_mem_pair,t.edge_ends]; simp
  · rintro ⟨e,he,hv⟩
    rw [← t.edge_range] at he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
    rw [D.incident_iff_mem_pair,t.edge_ends,Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · exact ⟨i,rfl⟩
    · exact ⟨i+1,rfl⟩

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.Triangle.corner_iff_incident := @_root_.OAI.Barnette.Network.Triangle.corner_iff_incident
