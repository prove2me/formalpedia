-- Prove2me | solution 1 for OAI.OneWayLiveness.CellNetwork.diagram_compatible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:33:21.482637+00:00
-- url     : https://prove2.me/submissions/a53f5c10-4375-4e9f-ba92-0ac4c7b5f7d2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Cells.lean:L117-L137
-- (upload_full_project.md Phase 4): solution for node OAI.OneWayLiveness.CellNetwork.diagram_compatible. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells

-- ---- from OAI.Combinatorics.Automata.Cells ----
namespace OAI

namespace OneWayLiveness
namespace Pairing
variable {P I : Type} [Fintype P] [Fintype I]

lemma transport_compatible {P Q C : Type*} (a : Pairing P) (e : P ≃ Q) (c : Q → C) :
    (a.transport e).Compatible c ↔ a.Compatible (c ∘ e) := by
  constructor
  · intro h x y hxy
    exact h (e x) (e y) (by simpa only [transport, Equiv.symm_apply_apply] using hxy)
  · intro h x y hxy
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h _ _ hxy

lemma close_compatible (lanes : Pairing (P ⊕ I)) (joins : Pairing I) (c : P → Bool) :
    (close lanes joins).Compatible c ↔
    ∃ f : I → Bool, lanes.Compatible (Sum.elim c f) ∧ joins.Compatible f := by
  rw [close, transport_compatible]
  have hc : c ∘ (Equiv.sumEmpty P Empty) = Sum.elim c (fun e => e.elim) := by
    funext p; cases p with | inl p => rfl | inr p => exact p.elim
  rw [hc, compose_compatible]
  apply exists_congr
  intro f
  rw [transport_compatible]
  rfl

lemma ofInvolution_compatible {P C : Type*} (f : P → P) (hf : Function.Involutive f)
    (hn : ∀ p, f p ≠ p) (c : P → C) :
    (ofInvolution f hf hn).Compatible c ↔ ∀ p, c p = c (f p) := by
  constructor
  · intro h p; exact h p (f p) rfl
  · intro h p q hpq; cases hpq; exact h p

end Pairing

namespace CellNetwork
variable (Q : Type)
lemma lanes_compatible (c : Boundary Q × Bool → Bool) (f : Tip Q → Bool) :
    (lanes Q).Compatible (Sum.elim c f) ↔
    (∀ b l, c (b,l) = f (.inl b, tipRole b.1 l)) ∧
    (∀ pq r t, f (.inr (pq,r),t) = f (.inr (pq,!r),!t)) := by
  rw [lanes, Pairing.ofInvolution_compatible]
  constructor
  · intro h; exact ⟨fun b l => h (.inl (b,l)), fun pq r t => h (.inr (.inr (pq,r),t))⟩
  · rintro ⟨hb, hs⟩ (⟨b,l⟩ | ⟨(b | ⟨pq,r⟩),t⟩)
    · exact hb b l
    · simpa only [laneMate, Sum.elim_inl, Sum.elim_inr, tipRole_twice] using (hb b (tipRole b.1 t)).symm
    · exact hs pq r t

lemma joins_compatible (r : Equiv.Perm (Incidence Q)) (f : Tip Q → Bool) :
    (joins Q r).Compatible f ↔ ∀ i, f (i,false) = f (r i,true) := by
  rw [joins, Pairing.ofInvolution_compatible]
  constructor
  · exact fun h i => h (i,false)
  · intro h ⟨i,b⟩
    cases b with
    | false => exact h i
    | true => simpa [joinMate] using (h (r.symm i)).symm

lemma diagram_compatible [Fintype Q] (r : Equiv.Perm (Incidence Q))
    (left right : Port Q → Bool) :
    (diagram Q r).Compatible (Sum.elim left right) ↔ ∃ f : Tip Q → Bool,
    (∀ s slot l, (if s then right else left) (slot,l) = f (.inl (s,slot),tipRole s l)) ∧
    (∀ pq role t, f (.inr (pq,role),t) = f (.inr (pq,!role),!t)) ∧
    (∀ i, f (i,false) = f (r i,true)) := by
  rw [diagram, Pairing.transport_compatible, Pairing.close_compatible]
  apply exists_congr
  intro f
  rw [lanes_compatible, joins_compatible, and_assoc]
  apply and_congr_left
  intro _
  constructor
  · intro h s slot l
    cases s with
    | false => simpa [portsEquiv] using h (false,slot) l
    | true => simpa [portsEquiv] using h (true,slot) l
  · intro h ⟨s,slot⟩ l
    cases s with
    | false => simpa [portsEquiv] using h false slot l
    | true => simpa [portsEquiv] using h true slot l

end CellNetwork
end OneWayLiveness

end OAI

-- ---- platform node ----
open OAI OAI.OneWayLiveness OAI.OneWayLiveness.CellNetwork


theorem solution : type_of% @_root_.OAI.OneWayLiveness.CellNetwork.diagram_compatible := @_root_.OAI.OneWayLiveness.CellNetwork.diagram_compatible
