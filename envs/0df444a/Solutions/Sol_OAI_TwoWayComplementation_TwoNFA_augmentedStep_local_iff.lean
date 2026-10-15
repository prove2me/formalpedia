-- Prove2me | solution 1 for OAI.TwoWayComplementation.TwoNFA.augmentedStep_local_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:20:07.914996+00:00
-- url     : https://prove2.me/submissions/b3a9e626-d7cd-4ffb-a6c7-3d12b11dfd43

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Normalization.lean:L135-L201
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.TwoNFA.augmentedStep_local_iff. The node keeps its source
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

/-- The global augmented graph is exactly the graph of the local moves and head displacement. -/
theorem augmentedStep_local_iff {Sigma Q : Type*} (A : TwoNFA Sigma Q) (w : List Sigma)
    (c d : Option Q × Fin (w.length + 3)) :
    (c, d) ∈ A.augmentedStep w ↔
      ∃ p : Fin (w.length + 2), c.2 = p.castSucc ∧ ∃ move : Fin 3,
        (c.1, d.1) ∈ A.augmentedMove (tapeSymbol w p) move ∧
        (d.2.val : ℤ) = (p.val : ℤ) + (move.val : ℤ) - 1 := by
  constructor
  · rintro (⟨⟨q, p⟩, ⟨r, t⟩, rfl, rfl, hstep⟩ |
      ⟨q, p, rfl, rfl, hq⟩ | ⟨hc, hd, hpos⟩)
    · obtain ⟨move, htrans, hpos⟩ := hstep
      change (t.val : ℤ) = (p.val : ℤ) + (move.val : ℤ) - 1 at hpos
      refine ⟨p, rfl, move, ⟨htrans, ?_, ?_⟩, hpos⟩
      · intro hleft hmove
        have hp := (tapeSymbol_left_iff w p).mp hleft
        have hm := congrArg Fin.val hmove
        simp only [Fin.val_zero] at hm
        omega
      · intro hright hmove
        have hp := (tapeSymbol_right_iff w p).mp hright
        have hm := congrArg Fin.val hmove
        norm_num at hm
        omega
    · exact ⟨p, rfl, 1, ⟨hq, rfl⟩, by simp⟩
    · let p : Fin (w.length + 2) := ⟨c.2.val, by have := d.2.isLt; omega⟩
      refine ⟨p, Fin.ext rfl, 2, ?_, ?_⟩
      · rw [hc, hd]
        exact rfl
      · dsimp [p]
        omega
  · rintro ⟨p, hpos, move, hlocal, hdisp⟩
    obtain ⟨cq, cp⟩ := c
    obtain ⟨dq, dp⟩ := d
    change cp = p.castSucc at hpos
    subst cp
    change (dp.val : ℤ) = (p.val : ℤ) + (move.val : ℤ) - 1 at hdisp
    cases cq with
    | none =>
      cases dq with
      | none =>
        change move = 2 at hlocal
        subst move
        exact Or.inr (Or.inr ⟨rfl, rfl, by simp only [Fin.val_castSucc]; norm_num at hdisp; omega⟩)
      | some r => exact hlocal.elim
    | some q =>
      cases dq with
      | none =>
        change q ∈ A.accepting ∧ move = 1 at hlocal
        obtain ⟨hq, rfl⟩ := hlocal
        refine Or.inr (Or.inl ⟨q, p, rfl, ?_, hq⟩)
        congr 1
        apply Fin.ext
        change dp.val = p.val
        norm_num at hdisp
        omega
      | some r =>
        change (r, move) ∈ A.transition q (tapeSymbol w p) ∧
          (tapeSymbol w p = Sum.inl 0 → move ≠ 0) ∧
          (tapeSymbol w p = Sum.inl 1 → move ≠ 2) at hlocal
        have hdp : dp.val < w.length + 2 := by
          by_contra hn
          have hdpval : dp.val = w.length + 2 := by omega
          have hpval : p.val = w.length + 1 := by have := move.isLt; omega
          have hm : move = 2 := Fin.ext (by have := move.isLt; omega)
          exact hlocal.2.2 ((tapeSymbol_right_iff w p).mpr hpval) hm
        refine Or.inl ⟨(q, p), (r, ⟨dp.val, hdp⟩), rfl, ?_, move, hlocal.1, hdisp⟩
        exact Prod.ext rfl (Fin.ext rfl)

end TwoNFA

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.TwoNFA
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.TwoNFA.augmentedStep_local_iff := @_root_.OAI.TwoWayComplementation.TwoNFA.augmentedStep_local_iff
