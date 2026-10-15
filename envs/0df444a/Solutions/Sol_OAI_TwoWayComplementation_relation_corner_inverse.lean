-- Prove2me | solution 1 for OAI.TwoWayComplementation.relation_corner_inverse
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:49:41.80171+00:00
-- url     : https://prove2.me/submissions/59a97f6a-e2d9-4876-aba5-4e742ea1b2bb

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/RelationMonoid.lean:L41-L69
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.relation_corner_inverse. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid

-- ---- from OAI.Combinatorics.TwoWayAutomata.RelationMonoid ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Restriction and extension are inverse on the two supported corners. -/
theorem relation_corner_inverse {α : Type*} (P i : SetRel α α)
    (hP : P ○ P = P) (hiPi : i ○ P ○ i = i) :
    (∀ Z, (P ○ i ○ P) ○ Z ○ (P ○ i ○ P) = Z → P ○ (i ○ Z ○ i) ○ P = Z) ∧
    (∀ A, i ○ A ○ i = A →
      (P ○ i ○ P) ○ (P ○ A ○ P) ○ (P ○ i ○ P) = P ○ A ○ P ∧
      i ○ (P ○ A ○ P) ○ i = A) := by
  have hPP (R : SetRel α α) : P ○ (P ○ R) = P ○ R := by
    rw [← SetRel.comp_assoc, hP]
  have hiPiR (R : SetRel α α) : i ○ (P ○ (i ○ R)) = i ○ R := by
    rw [← SetRel.comp_assoc i P, ← SetRel.comp_assoc, hiPi]
  constructor
  · intro Z hZ
    have hPZP : P ○ Z ○ P = Z := by
      conv_lhs => rw [← hZ]
      simpa only [SetRel.comp_assoc, hPP, hP] using hZ
    calc
      P ○ (i ○ Z ○ i) ○ P = P ○ (i ○ (P ○ Z ○ P) ○ i) ○ P := by rw [hPZP]
      _ = Z := by simpa only [SetRel.comp_assoc] using hZ
  · intro A hA
    constructor
    · calc
        (P ○ i ○ P) ○ (P ○ A ○ P) ○ (P ○ i ○ P) =
            P ○ (i ○ A ○ i) ○ P := by
              conv_lhs => rw [← hA]
              simp only [SetRel.comp_assoc, hPP, hiPiR]
        _ = P ○ A ○ P := by rw [hA]
    · conv_lhs => rw [← hA]
      simpa only [SetRel.comp_assoc, hiPiR, hiPi] using hA

namespace RelationMonoid

end RelationMonoid

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.relation_corner_inverse := @_root_.OAI.TwoWayComplementation.relation_corner_inverse
