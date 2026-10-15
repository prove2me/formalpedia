-- Prove2me | solution 1 for OAI.OneWayLiveness.Machine.positiveCopy_accepts
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:37:44.826836+00:00
-- url     : https://prove2.me/submissions/f19b62db-54d6-4e25-805b-30cede718f5e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Normalization.lean:L95-L114
-- (upload_full_project.md Phase 4): solution for node OAI.OneWayLiveness.Machine.positiveCopy_accepts. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization

-- ---- from OAI.Combinatorics.Automata.Normalization ----
namespace OAI

namespace OneWayLiveness

namespace Machine
variable {Alpha Q : Type}
variable (M : Machine Alpha Q)
end Machine

namespace Machine
variable {Alpha Q : Type} (M : Machine Alpha Q)

lemma positiveCopy_step (w : List Alpha) (i : Fin (w.length + 2)) (q : Option Q)
    (c' : Config (Q := Option Q) w) :
    M.positiveCopy.Step w (i, q) c' ↔
      ∃ r, c'.2 = some r ∧ M.Step w (i, q.getD M.initial) (c'.1, r) := by
  constructor
  · rintro ⟨d, hd, hr⟩
    change (M.transition _ _).map _ = some _ at hd
    obtain ⟨⟨r, e⟩, ht, he⟩ := Option.map_eq_some_iff.mp hd
    simp only [Prod.mk.injEq] at he
    exact ⟨r, he.1.symm, e, ht, he.2 ▸ hr⟩
  · rintro ⟨r, hr, d, ht, hd⟩
    refine ⟨d, ?_, hd⟩
    change (M.transition _ _).map _ = some _
    simp only [ht, Option.map_some, hr]

lemma positiveCopy_reach (w : List Alpha) (c c' : Config (Q := Q) w) :
    Relation.ReflTransGen (M.positiveCopy.Step w) (c.1, some c.2) (c'.1, some c'.2) ↔
      Relation.ReflTransGen (M.Step w) c c' := by
  have forward (a b : Config (Q := Option Q) w)
      (h : Relation.ReflTransGen (M.positiveCopy.Step w) a b) :
      ∀ q, a.2 = some q → ∃ r, b.2 = some r ∧
      Relation.ReflTransGen (M.Step w) (a.1, q) (b.1, r) := by
    induction h with
    | refl => exact fun q hq => ⟨q, hq, .refl⟩
    | @tail b d hab hbd ih =>
      intro q hq
      obtain ⟨r, hr, hpath⟩ := ih q hq
      obtain ⟨r', hr', hd⟩ := (M.positiveCopy_step w b.1 b.2 d).mp hbd
      exact ⟨r', hr', hpath.tail (by simpa only [hr, Option.getD_some] using hd)⟩
  constructor
  · intro h
    obtain ⟨r, hr, hp⟩ := forward _ _ h c.2 rfl
    cases Option.some.inj hr
    exact hp
  · intro h
    exact h.lift (fun a => (a.1, some a.2)) (fun a b hab =>
      (M.positiveCopy_step w a.1 (some a.2) _).mpr ⟨b.2, rfl, hab⟩)

lemma positiveCopy_accepts (w : List Alpha) :
    M.positiveCopy.Accepts false w ↔ M.Accepts true w := by
  simp only [Accepts, FiniteRun, Bool.false_eq_true, ↓reduceIte]
  constructor
  · rintro ⟨c, hpath, q, hq, hacc⟩
    rcases hpath.cases_head with he | ⟨v, hv, hvc⟩
    · have : c.2 = none := congrArg Prod.snd he.symm
      simp [this] at hq
    · obtain ⟨r, hr, hs⟩ := (M.positiveCopy_step w _ none v).mp hv
      have hvq : Relation.ReflTransGen (M.Step w) (v.1, r) (c.1, q) := by
        apply (M.positiveCopy_reach w (v.1, r) (c.1, q)).mp
        have hv : v = (v.1, some r) := Prod.ext rfl hr
        have hc : c = (c.1, some q) := Prod.ext rfl hq
        rwa [hv, hc] at hvc
      exact ⟨(c.1, q), Relation.TransGen.head' hs hvq, hacc⟩
  · rintro ⟨c, hpath, hacc⟩
    obtain ⟨v, hs, hvc⟩ := Relation.TransGen.head'_iff.mp hpath
    refine ⟨(c.1, some c.2), ?_, c.2, rfl, hacc⟩
    exact ((M.positiveCopy_reach w v c).mpr hvc).head
      ((M.positiveCopy_step w _ none (v.1, some v.2)).mpr ⟨v.2, rfl, hs⟩)

end Machine

namespace Machine
variable {Alpha Q : Type} (M : Machine Alpha Q)

end Machine
end OneWayLiveness

end OAI

-- ---- platform node ----
open OAI OAI.OneWayLiveness OAI.OneWayLiveness.Machine


theorem solution : type_of% @_root_.OAI.OneWayLiveness.Machine.positiveCopy_accepts := @_root_.OAI.OneWayLiveness.Machine.positiveCopy_accepts
