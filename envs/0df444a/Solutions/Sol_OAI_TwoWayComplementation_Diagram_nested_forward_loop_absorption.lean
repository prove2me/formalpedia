-- Prove2me | solution 1 for OAI.TwoWayComplementation.Diagram.nested_forward_loop_absorption
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:34:19.897175+00:00
-- url     : https://prove2.me/submissions/ca83a389-51ca-4bce-bedc-a9998310843f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Nesting.lean:L18-L85
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.Diagram.nested_forward_loop_absorption. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes

-- ---- from OAI.Combinatorics.TwoWayAutomata.Classes ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

theorem corner_returns {m : ℕ} (e z : Diagram m) (hz : z ∈ e.corner) :
    e.left ⊆ z.left ∧ e.right ⊆ z.right := by
  constructor
  · rw [← congrArg left hz.1]
    exact Set.subset_union_left
  · rw [← congrArg right hz.2]
    exact Set.subset_union_left

end Diagram

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Nesting ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

/-- Two finite-path rearrangements for absorption under nesting. -/
theorem nested_forward_loop_absorption {m : ℕ} (e d : Diagram m) (hd : d ∈ e.corner) :
    e.forward ○ d.loopClosure true ○ d.forward ⊆ d.loopClosure true ○ d.forward ∧
    d.forward ○ d.loopClosure true ○ e.forward ⊆ d.forward ○ d.loopClosure true := by
  let S := relStar (d.left ○ e.right)
  let T := relStar (e.left ○ d.right)
  obtain ⟨hL, hR⟩ := corner_returns e d hd
  have hS : S ⊆ d.loopClosure true := relStar_mono (SetRel.comp_subset_comp_right hR)
  have hT : T ⊆ d.loopClosure true := relStar_mono (SetRel.comp_subset_comp_left hL)
  have hF : e.forward ○ S ○ d.forward = d.forward := congrArg forward hd.1
  have hF' : d.forward ○ T ○ e.forward = d.forward := congrArg forward hd.2
  have hLd : e.left ∪ (e.forward ○ S ○ d.left ○ e.backward) = d.left :=
    congrArg left hd.1
  have hRd : e.right ∪ (e.backward ○ d.right ○ T ○ e.forward) = d.right :=
    congrArg right hd.2
  have hLpart : e.forward ○ S ○ d.left ○ e.backward ⊆ d.left :=
    Set.subset_union_right.trans hLd.le
  have hRpart : e.backward ○ d.right ○ T ○ e.forward ⊆ d.right :=
    Set.subset_union_right.trans hRd.le
  have hKleft : d.loopClosure true =
      S ○ relStar (d.left ○ e.backward ○ d.right ○ T ○ e.forward ○ S) := by
    change relStar (d.left ○ d.right) = _
    conv_lhs => rw [← hRd]
    simp only [S, relComp_union, relStar_union, SetRel.comp_assoc]
  have hKright : d.loopClosure true =
      T ○ relStar (e.forward ○ S ○ d.left ○ e.backward ○ d.right ○ T) := by
    change relStar (d.left ○ d.right) = _
    conv_lhs => rw [← hLd]
    simp only [T, union_relComp, relStar_union, SetRel.comp_assoc]
  have hleft : e.forward ○ S ○ d.left ○ e.backward ○ d.right ○ T ⊆
      d.loopClosure true := by
    calc
      _ ⊆ d.left ○ d.right ○ T := by gcongr
      _ ⊆ d.loopClosure true := by
        rintro ⟨x, y⟩ ⟨z, hxz, hzy⟩
        exact (hT hzy).head hxz
  have hright : S ○ d.left ○ e.backward ○ d.right ○ T ○ e.forward ⊆
      d.loopClosure true := by
    calc
      _ = S ○ d.left ○ (e.backward ○ d.right ○ T ○ e.forward) := by
        simp only [SetRel.comp_assoc]
      _ ⊆ S ○ d.left ○ d.right := by gcongr
      _ ⊆ d.loopClosure true := by
        rintro ⟨x, y⟩ ⟨z, ⟨p, hxp, hpz⟩, hzy⟩
        exact (hS hxp).tail ⟨z, hpz, hzy⟩
  have hleftStar : relStar (e.forward ○ S ○ d.left ○ e.backward ○ d.right ○ T) ⊆
      d.loopClosure true := fun _ h =>
    Relation.reflTransGen_closed (fun _ _ hab => hleft hab) _ _ h
  have hrightStar : relStar (S ○ d.left ○ e.backward ○ d.right ○ T ○ e.forward) ⊆
      d.loopClosure true := fun _ h =>
    Relation.reflTransGen_closed (fun _ _ hab => hright hab) _ _ h
  constructor
  · calc
      _ = relStar (e.forward ○ S ○ d.left ○ e.backward ○ d.right ○ T) ○
          (e.forward ○ S ○ d.forward) := by
        rw [hKleft]
        simpa only [SetRel.comp_assoc] using
          congrArg (· ○ d.forward)
            (comp_relStar_rotate (e.forward ○ S) (d.left ○ e.backward ○ d.right ○ T))
      _ ⊆ d.loopClosure true ○ d.forward := by rw [hF]; gcongr
  · calc
      _ = (d.forward ○ T ○ e.forward) ○
          relStar (S ○ d.left ○ e.backward ○ d.right ○ T ○ e.forward) := by
        rw [hKright]
        simpa only [SetRel.comp_assoc] using
          congrArg (d.forward ○ T ○ ·)
            (comp_relStar_rotate e.forward (S ○ d.left ○ e.backward ○ d.right ○ T)).symm
      _ ⊆ d.forward ○ d.loopClosure true := by rw [hF']; gcongr

end Diagram

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.Diagram.nested_forward_loop_absorption := @_root_.OAI.TwoWayComplementation.Diagram.nested_forward_loop_absorption
