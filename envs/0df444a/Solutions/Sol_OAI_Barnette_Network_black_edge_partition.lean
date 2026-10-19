-- Prove2me | solution 1 for OAI.Barnette.Network.black_edge_partition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:22:09.004888+00:00
-- url     : https://prove2.me/submissions/744b65db-785b-4580-a631-7fddc6a0e1db

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/MinorDuality.lean:L158-L177
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.black_edge_partition. The node keeps its source
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

-- ---- from OAI.Combinatorics.Hamiltonian.StateDisk ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

omit [Fintype V] [Fintype E] [Fintype F] in
lemma blackEndpoint_spec (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (e : E) :
    black (N.blackEndpoint black e) ∧ N.Incident e (N.blackEndpoint black e) := by
  by_cases ht : black (N.tail e)
  · simp only [blackEndpoint,ite_eq_left ht]; exact ⟨ht,Or.inl rfl⟩
  · simp only [blackEndpoint,ite_eq_right ht]
    exact ⟨not_not.mp (fun hh => ht ((hc e).mpr hh)),Or.inr rfl⟩

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

-- ---- from OAI.Combinatorics.Hamiltonian.MinorDuality ----
namespace OAI

/-! Exact duality under finite network minors. -/

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
lemma black_edge_partition (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (K : Finset E) :
    ∑ v ∈ Finset.univ.filter black, ((N.star v).filter fun e => e ∈ K).card = K.card := by
  have hstar : ∀ v, ((N.star v).filter fun e => e ∈ K) =
      K.filter fun e => N.Incident e v := by
    intro v; ext e; simp [star,and_comm]
  simp only [hstar,Finset.card_filter]
  rw [Finset.sum_comm]
  have he (e : E) : ∀ v, black v → (N.Incident e v ↔ N.blackEndpoint black e = v) := by
    intro v hv
    exact ⟨N.blackEndpoint_eq black hc hv,fun hh => hh ▸ (N.blackEndpoint_spec black hc e).2⟩
  conv_rhs => rw [Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro e _
  have hrewrite : ∀ v ∈ Finset.univ.filter black,
      (if N.Incident e v then 1 else 0 : ℕ) = if N.blackEndpoint black e = v then 1 else 0 := by
    intro v hv; rw [he e v ((Finset.mem_filter.mp hv).2)]
  rw [Finset.sum_congr rfl hrewrite]
  simp [(N.blackEndpoint_spec black hc e).1]

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.black_edge_partition := @_root_.OAI.Barnette.Network.black_edge_partition
