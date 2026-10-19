-- Prove2me | solution 1 for OAI.Barnette.Network.simple_of_cubic_stars
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:51:19.389601+00:00
-- url     : https://prove2.me/submissions/362a7cd4-9a91-406a-b7e2-8e7d3a4fc8da

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/ThreeCuts.lean:L304-L354
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.simple_of_cubic_stars. The node keeps its source
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

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

lemma simple_of_cubic_stars (hl : ∀ e, N.tail e ≠ N.head e)
    (hc : ∀ v, (N.star v).card = 3) (h3 : N.ThreeEdgeConnected)
    (hV : 3 ≤ Fintype.card V) : N.Simple := by
  refine ⟨hl,?_⟩
  intro e f hef
  by_contra hne
  dsimp only at hef
  let a := N.tail e
  let b := N.head e
  have hab : a ≠ b := hl e
  have hfa : N.Incident f a := (N.incident_iff_mem_pair f a).mpr (by rw [← hef]; simp [a])
  have hfb : N.Incident f b := (N.incident_iff_mem_pair f b).mpr (by rw [← hef]; simp [b])
  have hsa : ({e,f} : Finset E) ⊆ N.star a := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl|hk
    · exact (N.mem_star _ _).mpr (Or.inl rfl)
    · have hk' := Finset.mem_singleton.mp hk
      subst k
      exact (N.mem_star _ _).mpr hfa
  have hsb : ({e,f} : Finset E) ⊆ N.star b := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl|hk
    · exact (N.mem_star _ _).mpr (Or.inr rfl)
    · have hk' := Finset.mem_singleton.mp hk
      subst k
      exact (N.mem_star _ _).mpr hfb
  have hein : e ∉ N.cut {a,b} := by simp [mem_cut,a,b]
  have hfin : f ∉ N.cut {a,b} := by
    have hh := Sym2.eq_iff.mp hef
    rcases hh with ⟨ht,hh⟩|⟨ht,hh⟩ <;> simp [mem_cut,← ht,← hh,a,b]
  have hsub : N.cut {a,b} ⊆ (N.star a \ {e,f}) ∪ (N.star b \ {e,f}) := by
    intro k hk
    have hke : k ∉ ({e,f} : Finset E) := by
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
      exact ⟨fun hh => hein (hh ▸ hk),fun hh => hfin (hh ▸ hk)⟩
    have hi : N.Incident k a ∨ N.Incident k b := by
      have hh := (N.mem_cut {a,b} k).mp hk
      simp only [Finset.mem_insert,Finset.mem_singleton] at hh
      simp only [Incident]
      tauto
    exact hi.elim (fun hi => Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨(N.mem_star _ _).mpr hi,hke⟩))
      (fun hi => Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨(N.mem_star _ _).mpr hi,hke⟩))
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Finset.card_sdiff_of_subset hsa,Finset.card_sdiff_of_subset hsb,hc,hc] at hcard
  simp only [Finset.card_pair hne] at hcard
  have hout : ({a,b} : Finset V)ᶜ.Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_compl,Finset.card_pair hab]
    omega
  have hh := h3 {a,b} (by simp) hout
  omega

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


theorem solution : type_of% @_root_.OAI.Barnette.Network.simple_of_cubic_stars := @_root_.OAI.Barnette.Network.simple_of_cubic_stars
