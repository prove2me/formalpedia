-- Prove2me | solution 1 for OAI.TwoWayComplementation.word_diagram_order_reversal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:22:31.388306+00:00
-- url     : https://prove2.me/submissions/f7a853c3-1de7-4c42-8cab-28cecde9fd9a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Recognition.lean:L10-L34
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.word_diagram_order_reversal. The node keeps its source
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

-- ---- from OAI.Combinatorics.TwoWayAutomata.Diagram ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

theorem inclusion_refl {m : ℕ} (a : Diagram m) : (a, a) ∈ inclusion m :=
  ⟨Set.Subset.rfl, Set.Subset.rfl, Set.Subset.rfl, Set.Subset.rfl⟩

end Diagram

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Classes ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

theorem comp_mono {m : ℕ} {a a' b b' : Diagram m}
    (ha : (a, a') ∈ inclusion m) (hb : (b, b') ∈ inclusion m) :
    (comp a b, comp a' b') ∈ inclusion m := by
  obtain ⟨haf, hab, hal, har⟩ := ha
  obtain ⟨hbf, hbb, hbl, hbr⟩ := hb
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp [comp] <;> gcongr

end Diagram

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.RelationMonoid ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Singleton contexts test an individual relation edge. -/
theorem singleton_context {α : Type*} (R : SetRel α α) (p q : α) :
    restrictedIdentity {p} ○ R ○ restrictedIdentity {q} =
      {(x, y) | x = p ∧ y = q ∧ (p, q) ∈ R} := by
  ext ⟨x, y⟩
  simp [SetRel.comp, restrictedIdentity]
  aesop

namespace RelationMonoid

end RelationMonoid

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Source ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

theorem relationProduct_append {H : Type*} (u v : List (SetRel H H)) :
    relationProduct (u ++ v) = relationProduct u ○ relationProduct v := by
  induction u with
  | nil => simp [relationProduct]
  | cons R u ih => simpa [relationProduct, SetRel.comp_assoc] using congrArg (R ○ ·) ih

/-- Singleton letters on the two sides test one edge of a word's relation product. -/
theorem singleton_word_context {H : Type*} (w : List (SetRel H H)) (p q : H) :
    (relationProduct ([restrictedIdentity {p}] ++ w ++ [restrictedIdentity {q}])).Nonempty ↔
      (p, q) ∈ relationProduct w := by
  rw [relationProduct_append, relationProduct_append]
  simp only [relationProduct, List.foldr_cons, List.foldr_nil, SetRel.comp_id]
  rw [singleton_context]
  constructor
  · rintro ⟨⟨x, y⟩, _, _, hpq⟩
    exact hpq
  · intro hpq
    exact ⟨(p, q), rfl, rfl, hpq⟩

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Recognition ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Singleton contexts force reversal of relation inclusion. -/
theorem word_diagram_order_reversal {H : Type*} {m : ℕ}
    (τ : List (SetRel H H) → Diagram m)
    (hmul : ∀ u v, τ (u ++ v) = Diagram.comp (τ u) (τ v))
    (l r : Diagram m) (a b : Fin m)
    (hlanguage : ∀ w, (a, b) ∈ (Diagram.comp (Diagram.comp l (τ w)) r).forward ↔
      ¬ (relationProduct w).Nonempty)
    {u v : List (SetRel H H)} (huv : (τ u, τ v) ∈ Diagram.inclusion m) :
    relationProduct v ⊆ relationProduct u := by
  classical
  rintro ⟨p, q⟩ hpq
  by_contra hn
  let left := [restrictedIdentity {p}]
  let right := [restrictedIdentity {q}]
  have hU : ¬ (relationProduct (left ++ u ++ right)).Nonempty :=
    fun h => hn ((singleton_word_context u p q).mp h)
  have hV : (relationProduct (left ++ v ++ right)).Nonempty :=
    (singleton_word_context v p q).mpr hpq
  have hcontext : (τ (left ++ u ++ right), τ (left ++ v ++ right)) ∈ Diagram.inclusion m := by
    simp only [hmul]
    exact Diagram.comp_mono (Diagram.comp_mono (Diagram.inclusion_refl _) huv)
      (Diagram.inclusion_refl _)
  have hmarked := Diagram.comp_mono
    (Diagram.comp_mono (Diagram.inclusion_refl l) hcontext) (Diagram.inclusion_refl r)
  exact (hlanguage _).mp (hmarked.1 ((hlanguage _).mpr hU)) hV

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.word_diagram_order_reversal := @_root_.OAI.TwoWayComplementation.word_diagram_order_reversal
