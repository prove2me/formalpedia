-- Prove2me | solution 1 for OAI.Barnette.Network.sum_stars
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:38:41.707612+00:00
-- url     : https://prove2.me/submissions/d35974a3-1bf5-4577-bcbb-157ecf45c87e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/DiskRegions.lean:L269-L288
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.sum_stars. The node keeps its source
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

omit [Fintype V] in
lemma sum_stars (hN : N.Simple) (A : Finset V) :
    ∑ v ∈ A, (N.star v).card =
      ∑ e, ((if N.tail e ∈ A then 1 else 0) + (if N.head e ∈ A then 1 else 0)) := by
  calc
    ∑ v ∈ A, (N.star v).card =
      ∑ v ∈ A, ∑ e, ((if N.tail e = v then 1 else 0) + (if N.head e = v then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro v _
        rw [star,Finset.card_filter]
        simp only [Incident]
        apply Finset.sum_congr rfl
        intro e _
        have hne := hN.loopless e
        by_cases ht : N.tail e = v <;> by_cases hh : N.head e = v <;> simp_all
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      simp [Finset.sum_add_distrib]

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.sum_stars := @_root_.OAI.Barnette.Network.sum_stars
