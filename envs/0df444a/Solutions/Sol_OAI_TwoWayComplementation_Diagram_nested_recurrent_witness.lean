-- Prove2me | solution 1 for OAI.TwoWayComplementation.Diagram.nested_recurrent_witness
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:36:45.96125+00:00
-- url     : https://prove2.me/submissions/a8f22f8c-7b21-449c-a446-dec576e439a3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Nesting.lean:L169-L197
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.Diagram.nested_recurrent_witness. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_nested_forward_loop_absorption
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_rectangle_cover

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

theorem loopClosure_comp {m : ℕ} (e : Diagram m) (positive : Bool)
    (R : SetRel (Fin m) (Fin m)) :
    e.loopClosure positive ○ (e.loopClosure positive ○ R) = e.loopClosure positive ○ R := by
  rw [← SetRel.comp_assoc, loopClosure_comp_self]

end Diagram

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Nesting ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

theorem loopClosure_subset_of_corner {m : ℕ} (e d : Diagram m) (hd : d ∈ e.corner)
    (positive : Bool) : e.loopClosure positive ⊆ d.loopClosure positive := by
  obtain ⟨hL, hR⟩ := corner_returns e d hd
  cases positive
  · exact relStar_mono (SetRel.comp_subset_comp hR hL)
  · exact relStar_mono (SetRel.comp_subset_comp hL hR)

theorem nested_through_loop_absorption {m : ℕ} (e d : Diagram m) (hd : d ∈ e.corner)
    (positive : Bool) :
    e.through positive ○ d.loopClosure positive ○ d.through positive ⊆
      d.loopClosure positive ○ d.through positive ∧
    d.through positive ○ d.loopClosure positive ○ e.through positive ⊆
      d.through positive ○ d.loopClosure positive := by
  cases positive
  · have hreflect : reflect d ∈ (reflect e).corner :=
      ⟨by rw [← reflect_comp, hd.2], by rw [← reflect_comp, hd.1]⟩
    exact nested_forward_loop_absorption (reflect e) (reflect d) hreflect
  · exact nested_forward_loop_absorption e d hd

theorem nested_through_absorption {m : ℕ} (e d : Diagram m) (hd : d ∈ e.corner)
    (positive : Bool) :
    e.through positive ○ d.recurrence positive ⊆ d.recurrence positive ∧
    d.recurrence positive ○ e.through positive ⊆ d.recurrence positive := by
  obtain ⟨hl, hr⟩ := nested_through_loop_absorption e d hd positive
  constructor
  · simpa only [recurrence, SetRel.comp_assoc] using
      SetRel.comp_subset_comp_left (S := d.loopClosure positive) hl
  · simpa only [recurrence, SetRel.comp_assoc] using
      SetRel.comp_subset_comp_right (R := d.loopClosure positive) hr

theorem corner_forward_factor {m : ℕ} (e d : Diagram m) (he : comp e e = e)
    (hd : d ∈ e.corner) {u v : Fin m} (huv : (u, v) ∈ d.forward) :
    ∃ p q, (p, p) ∈ e.recurrence true ∧ (q, q) ∈ e.recurrence true ∧
      (u, p) ∈ e.forward ○ e.loopClosure true ∧ (p, q) ∈ e.surviving d true ∧
      (q, v) ∈ e.loopClosure true ○ e.forward := by
  let S := relStar (d.left ○ e.right)
  let T := relStar (e.left ○ d.right)
  have hF : e.forward ○ S ○ d.forward = d.forward := congrArg forward hd.1
  have hF' : d.forward ○ T ○ e.forward = d.forward := congrArg forward hd.2
  have hsplit : e.forward ○ S ○ d.forward ○ T ○ e.forward = d.forward := by rw [hF, hF']
  have hw : (u, v) ∈ e.forward ○ S ○ d.forward ○ T ○ e.forward := by rw [hsplit]; exact huv
  obtain ⟨a, ⟨b, ⟨c, ⟨f, huf, hfc⟩, hcb⟩, hba⟩, hav⟩ := hw
  obtain ⟨p, hpp, ⟨hup, hpf⟩⟩ := rectangle_cover e he (positive := true) huf
  obtain ⟨q, hqq, ⟨haq, hqv⟩⟩ := rectangle_cover e he (positive := true) hav
  refine ⟨p, q, hpp, hqq, hup, ?_, hqv⟩
  obtain ⟨r, hpr, hrf⟩ := hpf
  obtain ⟨s, has, hsq⟩ := haq
  change (p, q) ∈ e.loopClosure true ○ d.forward ○ e.loopClosure true
  rw [← hsplit]
  exact ⟨s, ⟨r, hpr, ⟨a, ⟨b, ⟨c, ⟨f, hrf, hfc⟩, hcb⟩, hba⟩, has⟩⟩, hsq⟩

theorem corner_through_factor {m : ℕ} (e d : Diagram m) (he : comp e e = e)
    (hd : d ∈ e.corner) {positive : Bool} {u v : Fin m}
    (huv : (u, v) ∈ d.through positive) :
    ∃ p q, (p, p) ∈ e.recurrence positive ∧ (q, q) ∈ e.recurrence positive ∧
      (u, p) ∈ e.through positive ○ e.loopClosure positive ∧
      (p, q) ∈ e.surviving d positive ∧
      (q, v) ∈ e.loopClosure positive ○ e.through positive := by
  cases positive
  · exact corner_forward_factor (reflect e) (reflect d)
      (by rw [← reflect_comp, he])
      ⟨by rw [← reflect_comp, hd.2], by rw [← reflect_comp, hd.1]⟩ huv
  · exact corner_forward_factor e d he hd huv

/-- A recurrent loop in a nested corner contains two recurrent points of its parent. -/
theorem nested_recurrent_witness {m : ℕ} (e d : Diagram m) (he : comp e e = e)
    (hd : d ∈ e.corner) {positive : Bool} {x : Fin m}
    (hxx : (x, x) ∈ d.recurrence positive) :
    ∃ p q, (p, p) ∈ e.recurrence positive ∧ (q, q) ∈ e.recurrence positive ∧
      (x, p) ∈ d.recurrence positive ∧ (p, x) ∈ d.recurrence positive ∧
      (x, q) ∈ d.recurrence positive ∧ (q, x) ∈ d.recurrence positive ∧
      (p, q) ∈ e.surviving d positive := by
  obtain ⟨v, ⟨u, hxu, huv⟩, hvx⟩ := hxx
  obtain ⟨p, q, hpp, hqq, ⟨a, hua, hap⟩, hpq, ⟨b, hqb, hbv⟩⟩ :=
    corner_through_factor e d he hd huv
  have hK := loopClosure_subset_of_corner e d hd positive
  obtain ⟨hFP, hPF⟩ := nested_through_absorption e d hd positive
  have hKP : d.loopClosure positive ○ d.recurrence positive ⊆ d.recurrence positive := by
    simp only [recurrence, SetRel.comp_assoc, loopClosure_comp, Set.Subset.rfl]
  have hPK : d.recurrence positive ○ d.loopClosure positive ⊆ d.recurrence positive := by
    simp only [recurrence, SetRel.comp_assoc, loopClosure_comp_self, Set.Subset.rfl]
  have hpqd : (p, q) ∈ d.recurrence positive :=
    (show e.surviving d positive ⊆ d.recurrence positive by
      unfold surviving recurrence; gcongr) hpq
  have hxpd : (x, p) ∈ d.recurrence positive :=
    hPK ⟨a, hPF ⟨u, hPK ⟨x, ⟨v, ⟨u, hxu, huv⟩, hvx⟩, hxu⟩, hua⟩, hK hap⟩
  have hpxd : (p, x) ∈ d.recurrence positive :=
    hPK ⟨v, hPF ⟨b, hPK ⟨q, hpqd, hK hqb⟩, hbv⟩, hvx⟩
  have hxqd : (x, q) ∈ d.recurrence positive :=
    hKP ⟨u, hxu, hFP ⟨a, hua, hKP ⟨p, hK hap, hpqd⟩⟩⟩
  have hqxd : (q, x) ∈ d.recurrence positive :=
    hKP ⟨b, hK hqb, hFP ⟨v, hbv, hKP ⟨x, hvx, ⟨v, ⟨u, hxu, huv⟩, hvx⟩⟩⟩⟩
  exact ⟨p, q, hpp, hqq, hxpd, hpxd, hxqd, hqxd, hpq⟩

end Diagram

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.Diagram.nested_recurrent_witness := @_root_.OAI.TwoWayComplementation.Diagram.nested_recurrent_witness
