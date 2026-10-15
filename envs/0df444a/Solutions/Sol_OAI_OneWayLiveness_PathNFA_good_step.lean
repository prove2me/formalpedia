-- Prove2me | solution 1 for OAI.OneWayLiveness.PathNFA.good_step
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:16:09.660715+00:00
-- url     : https://prove2.me/submissions/1c49f72b-1b77-4edb-9c8a-776eb3c252ad

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/PathNFA.lean:L136-L190
-- (upload_full_project.md Phase 4): solution for node OAI.OneWayLiveness.PathNFA.good_step. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_Automata_Rank
import Definitions.Def_OAI_Combinatorics_Automata_Diagram
import Definitions.Def_OAI_Combinatorics_Automata_Diagrams
import Definitions.Def_OAI_Combinatorics_Automata_Corners
import Definitions.Def_OAI_Combinatorics_Automata_Relations
import Definitions.Def_OAI_Combinatorics_Automata_RankLoss
import Definitions.Def_OAI_Combinatorics_Automata_Recognition
import Definitions.Def_OAI_Combinatorics_Automata_PathNFA

-- ---- from OAI.Combinatorics.Automata.PathNFA ----
namespace OAI

namespace OneWayLiveness

namespace NMachineOn
variable {Alpha Q : Type} (M : NMachineOn Alpha Q)
end NMachineOn

namespace PathNFA
variable {H : Type}
lemma scanned_letter_data (w : List (BRel H)) (i : Fin (w.length+2)) (R : BRel H)
    (hs : scanned w i = .letter R) : ∃ hi : i.val-1 < w.length, w[i.val-1] = R := by
  unfold scanned at hs
  split_ifs at hs with h0 hi
  exact ⟨by omega, Symbol.letter.inj hs⟩

lemma good_step (w : List (BRel H)) (c c' : NMachineOn.Config (Q := State H) w)
    (hg : Good w c) (hs : machine.Step w c c') : Good w c' := by
  rcases c with ⟨i,q⟩
  rcases c' with ⟨j,r⟩
  rcases hs with ⟨d,hd,hm⟩
  change (r,d) ∈ rules q (scanned w i) at hd
  cases q with
  | none =>
    change i.val = 0 at hg
    cases hb : scanned w i with
    | left =>
      rw [hb] at hd
      obtain ⟨p,he⟩ := hd
      have hr := congrArg Prod.fst he
      have hdir := congrArg Prod.snd he
      dsimp only at hr hdir
      subst r d
      change j.val = i.val+1 at hm
      change 1 ≤ j.val ∧ ∃ a, (w.take (j.val-1)).prod.holds a p
      refine ⟨by omega,p,?_⟩
      simp [show j.val-1 = 0 by omega]
    | letter R => simp [hb,rules] at hd
    | right => simp [hb,rules] at hd
  | some q =>
    cases q with
    | inl p =>
      obtain ⟨hip,a,ha⟩ := hg
      change 1 ≤ i.val at hip
      change (w.take (i.val-1)).prod.holds a p at ha
      cases hb : scanned w i with
      | left => simp [hb,rules] at hd
      | letter R =>
        rw [hb] at hd
        obtain ⟨q,he,hR⟩ := hd
        have hr := congrArg Prod.fst he
        have hdir := congrArg Prod.snd he
        dsimp only at hr hdir
        subst r d
        change j.val = i.val+1 at hm
        obtain ⟨hi,hRi⟩ := scanned_letter_data w i R hb
        change 1 ≤ j.val ∧ ∃ a, (w.take (j.val-1)).prod.holds a q
        refine ⟨by omega,a,?_⟩
        rw [show j.val-1 = (i.val-1)+1 by omega, List.take_succ_eq_append_getElem hi]
        simp only [List.prod_append, List.prod_cons, List.prod_nil, mul_one, BRel.mul_holds]
        exact ⟨p,ha,hRi ▸ hR⟩
      | right =>
        rw [hb] at hd
        have he : (r,d) = (accept,.stay) := hd
        have hr := congrArg Prod.fst he
        dsimp only at hr
        subst r
        change BRel.live w
        have hi := (scanned_eq_right_iff w i).mp hb
        exact ⟨a,p,by simpa only [hi,Nat.add_sub_cancel,List.take_length] using ha⟩
    | inr b => cases hb : scanned w i <;> simp [rules] at hd

end PathNFA

end OneWayLiveness

end OAI

-- ---- platform node ----
open OAI OAI.OneWayLiveness OAI.OneWayLiveness.PathNFA


theorem solution : type_of% @_root_.OAI.OneWayLiveness.PathNFA.good_step := @_root_.OAI.OneWayLiveness.PathNFA.good_step
