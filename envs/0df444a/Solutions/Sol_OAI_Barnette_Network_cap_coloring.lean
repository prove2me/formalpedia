-- Prove2me | solution 1 for OAI.Barnette.Network.cap_coloring
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:53:14.842049+00:00
-- url     : https://prove2.me/submissions/f8d05276-2d12-436a-b147-d4faaca45cd3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/ThreeCuts.lean:L385-L415
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.cap_coloring. The node keeps its source
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
import Theorems.Thm_OAI_Barnette_Network_cubic_black_region_count
import Theorems.Thm_OAI_Barnette_Network_cubic_region_count

-- ---- from OAI.Combinatorics.Hamiltonian.ThreeCuts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

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

lemma threeCut_black_card (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hb : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (A : Finset V) (hA : (N.cut A).card = 3) :
    (N.blackCut black A).card = 0 ∨ (N.blackCut black A).card = 3 := by
  have h₁ := N.cubic_region_count hN hc A
  have h₂ := N.cubic_black_region_count hN hc black hb A
  have h₃ := Finset.card_le_card (Finset.filter_subset (fun e => N.blackEndpoint black e ∈ A) (N.cut A))
  change (N.blackCut black A).card ≤ (N.cut A).card at h₃
  omega

lemma cap_coloring (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hb : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (A : Finset V) (hA : (N.cut A).card = 3) :
    ∀ e, N.capBlack black A ((N.cap A).tail e) ↔ ¬N.capBlack black A ((N.cap A).head e) := by
  intro e
  have hm := (N.mem_regionEdges A e.val).mp e.property
  have hcol := hb e.val
  have hboundary : e.val ∈ N.cut A →
      ((N.blackCut black A).card = 0 ↔ N.blackEndpoint black e.val ∉ A) := by
    intro he
    rcases N.threeCut_black_card hN hc black hb A hA with hz|hf
    · have hn : N.blackEndpoint black e.val ∉ A := by
        intro hh
        have hh' : e.val ∈ N.blackCut black A := Finset.mem_filter.mpr ⟨he,hh⟩
        rw [Finset.card_eq_zero.mp hz] at hh'
        exact Finset.notMem_empty _ hh'
      simp [hz,hn]
    · have heq : N.blackCut black A = N.cut A :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
      have hh := (Finset.mem_filter.mp (show e.val ∈ N.blackCut black A by rw [heq]; exact he)).2
      simp [hf,hh]
  change N.capBlack black A (N.capMap A (N.tail e.val)) ↔ ¬N.capBlack black A (N.capMap A (N.head e.val))
  by_cases ht : N.tail e.val ∈ A <;> by_cases hh : N.head e.val ∈ A
  · simpa only [capMap,dite_eq_left ht,dite_eq_left hh,capBlack] using hcol
  · have he : e.val ∈ N.cut A := (N.mem_cut A e.val).mpr (Or.inl ⟨ht,hh⟩)
    simp only [capMap,dite_eq_left ht,dite_eq_right hh,capBlack,hboundary he]
    by_cases hb' : black (N.tail e.val) <;> simp [blackEndpoint,hb',ht,hh]
  · have he : e.val ∈ N.cut A := (N.mem_cut A e.val).mpr (Or.inr ⟨hh,ht⟩)
    simp only [capMap,dite_eq_right ht,dite_eq_left hh,capBlack,hboundary he]
    by_cases hb' : black (N.tail e.val) <;> simp [blackEndpoint,hb',ht,hh] at hcol ⊢ <;> tauto
  · exact (hm.elim ht hh).elim
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


theorem solution : type_of% @_root_.OAI.Barnette.Network.cap_coloring := @_root_.OAI.Barnette.Network.cap_coloring
