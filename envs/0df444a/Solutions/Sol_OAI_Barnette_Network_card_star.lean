-- Prove2me | solution 1 for OAI.Barnette.Network.card_star
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:25:51.263694+00:00
-- url     : https://prove2.me/submissions/b270a3a9-ea58-4b49-b94c-7122730448b1

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/FlowCircuits.lean:L164-L186
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.card_star. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits

-- ---- from OAI.Combinatorics.Hamiltonian.FlowCircuits ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Minimal flow circuits, triangular faces, and simple cycle coordinates. -/

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

omit [Fintype V] [Fintype E] in
lemma otherEnd_spec (h : N.Simple) {e : E} {v : V} (hi : N.Incident e v) :
    v ≠ N.otherEnd e v ∧ s(N.tail e,N.head e) = s(v,N.otherEnd e v) := by
  rcases hi with ht | hh
  · rw [otherEnd,ite_eq_left ht]
    exact ⟨ht ▸ h.loopless e, by rw [ht]⟩
  · by_cases ht : N.tail e = v
    · exact (h.loopless e (ht.trans hh.symm)).elim
    · rw [otherEnd,ite_eq_right ht]
      exact ⟨hh ▸ (h.loopless e).symm, by rw [hh,Sym2.eq_swap]⟩

omit [Fintype V] [Fintype E] in
lemma otherEnd_adj (h : N.Simple) {e : E} {v : V} (hi : N.Incident e v) :
    N.graph.Adj v (N.otherEnd e v) := by
  obtain ⟨hne,he⟩ := N.otherEnd_spec h hi
  exact ⟨hne,e,Sym2.eq_iff.mp he⟩

lemma card_star (h : N.Simple) (v : V) : (N.star v).card = N.graph.degree v := by
  let f : {e // e ∈ N.star v} → N.graph.neighborSet v := fun e =>
    ⟨N.otherEnd e.val v, N.otherEnd_adj h ((N.mem_star _ _).mp e.property)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro e k hek
      apply Subtype.ext
      apply h.pair_injective
      change s(N.tail e.val, N.head e.val) = s(N.tail k.val, N.head k.val)
      rw [(N.otherEnd_spec h ((N.mem_star _ _).mp e.property)).2,
        (N.otherEnd_spec h ((N.mem_star _ _).mp k.property)).2]
      exact congrArg (fun w => s(v,w)) (congrArg Subtype.val hek)
    · intro w
      obtain ⟨hne,e,he⟩ := w.property
      have hi : N.Incident e v := he.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
      refine ⟨⟨e,(N.mem_star _ _).mpr hi⟩,Subtype.ext ?_⟩
      change N.otherEnd e v = w.val
      rcases he with ⟨ht,hh⟩ | ⟨ht,hh⟩
      · simp only [otherEnd,ht,ite_true,hh]
      · have ht' : N.tail e ≠ v := by rw [ht]; exact hne.symm
        rw [otherEnd,ite_eq_right ht',ht]
  have hh := Fintype.card_congr (Equiv.ofBijective f hf)
  simpa only [Fintype.card_coe, SimpleGraph.card_neighborSet_eq_degree] using hh

end
end Barnette.Network
namespace Barnette

open Fin.NatCast

namespace CycleCoordinates

variable {V : Type*} {G : SimpleGraph V} (C : CycleCoordinates G)

end CycleCoordinates
end Barnette

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E]
  (N : Network V E) (C : Barnette.CycleCoordinates N.graph)

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.card_star := @_root_.OAI.Barnette.Network.card_star
