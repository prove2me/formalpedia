-- Prove2me | solution 1 for OAI.Barnette.Network.white_positive_of_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:53:55.073286+00:00
-- url     : https://prove2.me/submissions/fde91cc6-7983-4120-bfe0-ef33068a51cf

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Circulation.lean:L226-L248
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.white_positive_of_boundary. The node keeps its source
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

-- ---- from OAI.Combinatorics.Hamiltonian.Circulation ----
namespace OAI

/-! Oriented triangular faces and positive white-face charges. -/

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

omit [Fintype V] [Fintype F] in
lemma white_positive_of_boundary (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (A : Finset V)
    (hcount : (N.cut A).card = 2 * (N.blackCut black A).card + 3) :
    0 < (A.filter fun v => ¬black v).card := by
  by_contra hn
  have hz : (A.filter fun v => ¬black v) = ∅ := Finset.card_eq_zero.mp (by omega)
  have hb : ∀ v ∈ A, black v := by
    intro v hv
    by_contra hnv
    have hh : v ∈ A.filter (fun v => ¬black v) := Finset.mem_filter.mpr ⟨hv,hnv⟩
    rw [hz] at hh
    exact Finset.notMem_empty _ hh
  have hEq : N.blackCut black A = N.cut A := by
    apply Finset.filter_eq_self.mpr
    intro e he
    rcases (N.mem_cut A e).mp he with ht | hh
    · rw [N.blackEndpoint_eq black hc (hb _ ht.1) (Or.inl rfl)]
      exact ht.1
    · rw [N.blackEndpoint_eq black hc (hb _ hh.1) (Or.inr rfl)]
      exact hh.1
  rw [hEq] at hcount
  omega

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.white_positive_of_boundary := @_root_.OAI.Barnette.Network.white_positive_of_boundary
