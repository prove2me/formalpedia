-- Prove2me | solution 1 for OAI.OneWayLiveness.CellNetwork.graph_step_from_state
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:39:30.149985+00:00
-- url     : https://prove2.me/submissions/86a2be30-6303-471f-adc5-add77311a139

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Network.lean:L291-L354
-- (upload_full_project.md Phase 4): solution for node OAI.OneWayLiveness.CellNetwork.graph_step_from_state. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network

-- ---- from OAI.Combinatorics.Automata.Network ----
namespace OAI

namespace OneWayLiveness
namespace CellNetwork
variable (Q : Type)

variable {Q} {Alpha : Type} (M : Machine Alpha Q)

lemma sourceAttach_eq_state (b : Symbol Alpha) (k : Key Q) (p : Q) :
    sourceAttach M b k = .inl p ↔ k.2.1 = p ∧ M.transition p b = some (k.2.2,k.1) := by
  classical
  simp only [sourceAttach]
  split_ifs with hk
  · simp only [Sum.inl.injEq]
    constructor
    · intro h; exact ⟨h, h ▸ hk⟩
    · exact And.left
  · constructor
    · intro h; cases h
    · rintro ⟨h, hh⟩; exact (hk (h.symm ▸ hh)).elim

variable (Q)
variable {Q}

lemma graph_step_from_state (finish : Q) (w : List Alpha) (c : Machine.Config (Q := Q) w)
    (v : Vertex Q w.length) :
    (graph M finish w).Step (stateVertex w c) v ↔
      ∃ c', v = stateVertex w c' ∧ M.Step w c c' := by
  classical
  constructor
  · rintro ⟨e, hs, hd⟩
    rcases c with ⟨i,p⟩
    rcases e with ⟨j,⟨dir,p',q⟩⟩ | (⟨j,⟨p',q⟩⟩ | z)
    · cases dir with
      | false =>
        change Sum.inl (j.succ,sourceAttach M (scanned w j.succ) (.left,p',q)) =
          Sum.inl (i,Sum.inl p) at hs
        have he := Sum.inl.inj hs
        have hi : j.succ = i := congrArg Prod.fst he
        subst i
        obtain ⟨hp, ht⟩ := (sourceAttach_eq_state M _ _ _).mp (congrArg Prod.snd he)
        exact ⟨(j.castSucc,q), hd.symm, .left, ht, rfl⟩
      | true =>
        change Sum.inl (j.castSucc,sourceAttach M (scanned w j.castSucc) (.right,p',q)) =
          Sum.inl (i,Sum.inl p) at hs
        have he := Sum.inl.inj hs
        have hi : j.castSucc = i := congrArg Prod.fst he
        subst i
        obtain ⟨hp, ht⟩ := (sourceAttach_eq_state M _ _ _).mp (congrArg Prod.snd he)
        exact ⟨(j.succ,q), hd.symm, .right, ht, rfl⟩
    · change Sum.inl (j,sourceAttach M (scanned w j) (.stay,p',q)) =
        Sum.inl (i,Sum.inl p) at hs
      have he := Sum.inl.inj hs
      have hi : j = i := congrArg Prod.fst he
      subst i
      obtain ⟨hp, ht⟩ := (sourceAttach_eq_state M _ _ _).mp (congrArg Prod.snd he)
      exact ⟨(j,q), hd.symm, .stay, ht, rfl⟩
    · cases hs
  · rintro ⟨⟨j,q⟩, rfl, d, ht, hr⟩
    rcases c with ⟨i,p⟩
    cases d with
    | left =>
      change j.val + 1 = i.val at hr
      let k : Fin (w.length + 1) := ⟨j.val, by omega⟩
      have hk : k.succ = i := Fin.ext hr
      refine ⟨.inl (k,(false,p,q)), ?_, ?_⟩
      · change Sum.inl (k.succ,sourceAttach M (scanned w k.succ) (.left,p,q)) = _
        rw [hk]
        rw [(sourceAttach_eq_state M _ _ _).mpr ⟨rfl, ht⟩]
        rfl
      · rfl
    | stay =>
      have hj : j = i := Fin.ext hr
      subst j
      refine ⟨.inr (.inl (i,(p,q))), ?_, rfl⟩
      change Sum.inl (i,sourceAttach M (scanned w i) (.stay,p,q)) = _
      rw [(sourceAttach_eq_state M _ _ _).mpr ⟨rfl, ht⟩]
      rfl
    | right =>
      change j.val = i.val + 1 at hr
      let k : Fin (w.length + 1) := ⟨i.val, by omega⟩
      have hk : k.succ = j := Fin.ext hr.symm
      refine ⟨.inl (k,(true,p,q)), ?_, ?_⟩
      · change Sum.inl (i,sourceAttach M (scanned w i) (.right,p,q)) = _
        rw [(sourceAttach_eq_state M _ _ _).mpr ⟨rfl, ht⟩]
        rfl
      · change stateVertex w (k.succ,q) = _
        rw [hk]

end CellNetwork
end OneWayLiveness

end OAI

-- ---- platform node ----
open OAI OAI.OneWayLiveness OAI.OneWayLiveness.CellNetwork


theorem solution : type_of% @_root_.OAI.OneWayLiveness.CellNetwork.graph_step_from_state := @_root_.OAI.OneWayLiveness.CellNetwork.graph_step_from_state
