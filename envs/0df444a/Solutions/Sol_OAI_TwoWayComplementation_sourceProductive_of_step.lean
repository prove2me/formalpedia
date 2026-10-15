-- Prove2me | solution 1 for OAI.TwoWayComplementation.sourceProductive_of_step
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:21:19.886623+00:00
-- url     : https://prove2.me/submissions/40864047-286a-46a2-b5f3-b4b346301965

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Source.lean:L46-L94
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.sourceProductive_of_step. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Normalization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Source

-- ---- from OAI.Combinatorics.TwoWayAutomata.Source ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

theorem sourceProductive_of_step {H : Type*} (w : List (SetRel H H))
    {c d : Option (Option H) × Fin (w.length + 2)}
    (hstep : (c, d) ∈ (sourceAutomaton H).step w) (hd : d ∈ sourceProductive w) :
    c ∈ sourceProductive w := by
  obtain ⟨cs, ci⟩ := c
  obtain ⟨ds, di⟩ := d
  obtain ⟨move, htransition, hpos⟩ := hstep
  change (ds, move) ∈ (sourceAutomaton H).transition cs (tapeSymbol w ci) at htransition
  change (di.val : ℤ) = (ci.val : ℤ) + (move.val : ℤ) - 1 at hpos
  cases cs with
  | none =>
    by_cases hleft : ci.val = 0
    · have hex : ∃ p, ds = some (some p) ∧ move = 2 := by
        simpa [sourceAutomaton, tapeSymbol, hleft] using htransition
      obtain ⟨p, hds, hmove⟩ := hex
      subst ds
      subst move
      have hdi : di.val = 1 := by norm_num at hpos; omega
      obtain ⟨_, q, hpq⟩ := hd
      exact ⟨hleft, (p, q), by simpa [hdi] using hpq⟩
    · by_cases hright : ci.val = w.length + 1 <;>
        simp [sourceAutomaton, tapeSymbol, hleft, hright] at htransition
  | some state =>
    cases state with
    | none =>
      change (ds, move) ∈ (∅ : Set (Option (Option H) × Fin 3)) at htransition
      exact htransition.elim
    | some p =>
      by_cases hleft : ci.val = 0
      · simp [sourceAutomaton, tapeSymbol, hleft] at htransition
      · by_cases hright : ci.val = w.length + 1
        · change 1 ≤ ci.val ∧ ∃ q, (p, q) ∈ relationProduct (w.drop (ci.val - 1))
          refine ⟨by omega, p, ?_⟩
          simp [hright, relationProduct]
        · have hex : ∃ q, (p, q) ∈ w[ci.val - 1]'(by omega) ∧
              ds = some (some q) ∧ move = 2 := by
            simpa [sourceAutomaton, tapeSymbol, hleft, hright] using htransition
          obtain ⟨q, hpq, hds, hmove⟩ := hex
          subst ds
          subst move
          have hdi : di.val = ci.val + 1 := by norm_num at hpos; omega
          obtain ⟨_, r, hqr⟩ := hd
          change 1 ≤ ci.val ∧ ∃ r, (p, r) ∈ relationProduct (w.drop (ci.val - 1))
          refine ⟨by omega, r, ?_⟩
          rw [List.drop_eq_getElem_cons (show ci.val - 1 < w.length from by omega)]
          change (p, r) ∈ w[ci.val - 1] ○ relationProduct (w.drop (ci.val - 1 + 1))
          refine ⟨q, hpq, ?_⟩
          simpa only [hdi, Nat.add_sub_cancel,
            Nat.sub_add_cancel (show 1 ≤ ci.val by omega)] using hqr

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.sourceProductive_of_step := @_root_.OAI.TwoWayComplementation.sourceProductive_of_step
