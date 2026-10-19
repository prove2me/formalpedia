-- Prove2me | solution 1 for OAI.Barnette.Network.cubic_region_count
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:40:07.695+00:00
-- url     : https://prove2.me/submissions/9836c0bb-ec41-4ae1-ae5f-e22925041356

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/DiskRegions.lean:L290-L303
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.cubic_region_count. The node keeps its source
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
import Theorems.Thm_OAI_Barnette_Network_card_star
import Theorems.Thm_OAI_Barnette_Network_sum_stars

-- ---- from OAI.Combinatorics.Hamiltonian.DiskRegions ----
namespace OAI

/-! Connected face regions and the exact disk Euler formula. -/

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

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

lemma cubic_region_count (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3) (A : Finset V) :
    3 * A.card + (N.cut A).card = 2 * (N.regionEdges A).card := by
  have hsum := N.sum_stars hN A
  have hv : (∑ v ∈ A, (N.star v).card) = 3 * A.card := by
    have hc' : ∀ v, N.graph.degree v = 3 := hc
    simp only [N.card_star hN,hc']
    simp [Nat.mul_comm]
  rw [hv] at hsum
  rw [hsum]
  simp only [cut,regionEdges,Finset.card_filter,
    ← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases ht : N.tail e ∈ A <;> by_cases hh : N.head e ∈ A <;> simp [ht,hh]

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.cubic_region_count := @_root_.OAI.Barnette.Network.cubic_region_count
