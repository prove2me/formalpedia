-- Prove2me | solution 1 for OAI.Barnette.Network.cubic_black_region_count
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:43:17.948855+00:00
-- url     : https://prove2.me/submissions/b56e3822-03f1-4dbc-afca-d98b4c21cff0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/StateDisk.lean:L242-L262
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.cubic_black_region_count. The node keeps its source
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
import Theorems.Thm_OAI_Barnette_Network_card_star
import Theorems.Thm_OAI_Barnette_Network_sum_stars

-- ---- from OAI.Combinatorics.Hamiltonian.StateDisk ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Minimal links, incidence states, and the signed disk identity. -/

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

omit [Fintype F] in
lemma cubic_black_region_count (sN : N.Simple) (hdeg : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (A : Finset V) :
    3 * (A.filter black).card + (N.cut A).card =
      (N.regionEdges A).card + (N.blackCut black A).card := by
  have hs := N.sum_stars sN (A.filter black)
  have hd : ∀ v, N.graph.degree v = 3 := hdeg
  have hh : (∑ v ∈ A.filter black, (N.star v).card) = 3 * (A.filter black).card := by
    simp only [N.card_star sN,hd]
    simp [Nat.mul_comm]
  rw [hh] at hs
  rw [hs]
  simp only [cut,regionEdges,blackCut,Finset.card_filter,Finset.mem_filter,
    Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hcol := hc e
  by_cases ht : N.tail e ∈ A <;> by_cases hh : N.head e ∈ A <;>
    by_cases hb : black (N.tail e) <;> by_cases hw : black (N.head e) <;>
    simp_all [blackEndpoint]

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.cubic_black_region_count := @_root_.OAI.Barnette.Network.cubic_black_region_count
