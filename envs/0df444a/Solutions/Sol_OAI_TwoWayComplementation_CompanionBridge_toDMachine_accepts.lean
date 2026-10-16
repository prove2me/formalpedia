-- Prove2me | solution 1 for OAI.TwoWayComplementation.CompanionBridge.toDMachine_accepts
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:08:02.777991+00:00
-- url     : https://prove2.me/submissions/0cc4253b-3801-438b-8189-c50152014ad7

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/TransitionBridge.lean:L123-L137
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.CompanionBridge.toDMachine_accepts. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Normalization__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Source__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Network__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Chain__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Tape__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Main
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationBridge
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_TransitionBridge

-- ---- from OAI.Combinatorics.TwoWayAutomata.Normalization ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Only the first tape position carries the left endmarker. -/
theorem tapeSymbol_left_iff {Sigma : Type*} (w : List Sigma) (p : Fin (w.length + 2)) :
    tapeSymbol w p = Sum.inl 0 ↔ p.val = 0 := by
  unfold tapeSymbol
  split_ifs <;> simp_all

/-- Only the last original tape position carries the right endmarker. -/
theorem tapeSymbol_right_iff {Sigma : Type*} (w : List Sigma) (p : Fin (w.length + 2)) :
    tapeSymbol w p = Sum.inl 1 ↔ p.val = w.length + 1 := by
  unfold tapeSymbol
  split_ifs <;> simp_all

namespace TwoNFA

end TwoNFA

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.TransitionBridge ----
namespace OAI

namespace TwoWayComplementation.CompanionBridge

open OneWayLiveness

theorem encode_scanned {Alpha : Type*} (w : List Alpha) (p : Fin (w.length + 2)) :
    encodeSymbol (scanned w p) = tapeSymbol w p := by
  unfold scanned tapeSymbol
  split_ifs <;> simp_all [encodeSymbol] <;> omega

theorem move_rel_iff (m : Move) (i j : ℕ) :
    m.Rel i j ↔ (j : ℤ) = (i : ℤ) + ((encodeMove m).val : ℤ) - 1 := by
  cases m <;> simp [Move.Rel, encodeMove] <;> omega

theorem guard_of_legal_move {Alpha : Type*} (w : List Alpha)
    (p r : Fin (w.length + 2)) (m : Move) (h : m.Rel p.val r.val) :
    Guard (scanned w p) m := by
  constructor
  · intro hs hm
    subst m
    have hp : p.val = 0 := (tapeSymbol_left_iff w p).mp (by
      rw [← encode_scanned, hs]; rfl)
    simp only [Move.Rel] at h
    omega
  · intro hs hm
    subst m
    have hp : p.val = w.length + 1 := (tapeSymbol_right_iff w p).mp (by
      rw [← encode_scanned, hs]; rfl)
    simp only [Move.Rel] at h
    omega

theorem toDMachine_step {Alpha : Type*} {s : ℕ}
    (A : TwoNFA Alpha (Fin s)) (hA : A.Deterministic) (w : List Alpha)
    (c d : Fin s × Fin (w.length + 2)) :
    (toDMachine A hA).Step w (c.2, c.1) (d.2, d.1) ↔ (c, d) ∈ A.step w := by
  change (∃ m, select (convertedTransitions A c.1 (scanned w c.2)) = some (d.1, m) ∧
    m.Rel c.2.val d.2.val) ↔ _
  simp only [select_eq_some_iff _ (convertedTransitions_subsingleton A hA _ _)]
  constructor
  · rintro ⟨m, hm, hrel⟩
    refine ⟨encodeMove m, ?_, (move_rel_iff m _ _).mp hrel⟩
    simpa only [encode_scanned] using hm.1
  · rintro ⟨m, hm, hrel⟩
    have hr : (decodeMove m).Rel c.2.val d.2.val := by
      rw [move_rel_iff, encode_decode]
      exact hrel
    refine ⟨decodeMove m, ⟨?_, guard_of_legal_move w c.2 d.2 _ hr⟩, hr⟩
    simpa only [encode_decode, encode_scanned] using hm

theorem toDMachine_accepts {Alpha : Type*} {s : ℕ}
    (A : TwoNFA Alpha (Fin s)) (hA : A.Deterministic) (w : List Alpha) :
    (toDMachine A hA).Accepts false w ↔ w ∈ A.language := by
  constructor
  · rintro ⟨⟨p, q⟩, hr, hq⟩
    refine ⟨(q, p), hq, ?_⟩
    change Relation.ReflTransGen ((toDMachine A hA).Step w) _ _ at hr
    exact hr.lift (fun c => (c.2, c.1))
      (p := fun c d => (c, d) ∈ A.step w) (fun c d h =>
        (toDMachine_step A hA w (c.2, c.1) (d.2, d.1)).mp h)
  · rintro ⟨⟨q, p⟩, hq, hr⟩
    refine ⟨(p, q), ?_, hq⟩
    exact hr.lift (fun c => (c.2, c.1))
      (p := (toDMachine A hA).Step w) (fun c d h =>
        (toDMachine_step A hA w c d).mpr h)

end TwoWayComplementation.CompanionBridge

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.CompanionBridge
open OneWayLiveness


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.CompanionBridge.toDMachine_accepts := @_root_.OAI.TwoWayComplementation.CompanionBridge.toDMachine_accepts
