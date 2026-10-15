-- Prove2me | solution 1 for OAI.OneWayLiveness.RectangleFrame.rel_mul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:53:34.956978+00:00
-- url     : https://prove2.me/submissions/e9fc1cee-fe64-4e51-80fa-6cc1c672e6ac

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Relations.lean:L203-L219
-- (upload_full_project.md Phase 4): solution for node OAI.OneWayLiveness.RectangleFrame.rel_mul. The node keeps its source
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

-- ---- from OAI.Combinatorics.Automata.Relations ----
namespace OAI

namespace OneWayLiveness

namespace BRel
variable {H : Type*}

end BRel

namespace BRel
variable {H : Type*}
end BRel

namespace RectangleFrame
variable {H I J : Type*} (F : RectangleFrame H I J)
lemma rel_mul (E D : Set (I × J)) : F.rel E * F.rel D = F.rel (E ∪ D) := by
  ext x y
  constructor
  · rintro ⟨k, (⟨hx, hn⟩ | ⟨p, hp, hx, hk⟩), hy⟩
    · subst k
      rcases hy with ⟨hxy, _⟩ | ⟨p, hp, hp1, hp2⟩
      · exact Or.inl ⟨hxy, hn⟩
      · exact Or.inr ⟨p, Or.inr hp, hp1, hp2⟩
    · rcases hy with ⟨hky, _⟩ | ⟨q, _hq, hq1, _hq2⟩
      · exact Or.inr ⟨p, Or.inl hp, hx, hky.symm.trans hk⟩
      · exact (F.disjoint q.1 p.2 (hq1.symm.trans hk)).elim
  · rintro (⟨rfl, hn⟩ | ⟨p, hp | hp, rfl, rfl⟩)
    · exact ⟨x, Or.inl ⟨rfl, hn⟩, Or.inl ⟨rfl, hn⟩⟩
    · exact ⟨F.right p.2, Or.inr ⟨p, hp, rfl, rfl⟩,
        Or.inl ⟨rfl, F.right_ne_hub p.2⟩⟩
    · exact ⟨F.left p.1, Or.inl ⟨rfl, F.left_ne_hub p.1⟩,
        Or.inr ⟨p, hp, rfl, rfl⟩⟩

end RectangleFrame

namespace Corner
variable {M : Type*} [Monoid M] {e : M} {he : e * e = e}

end Corner

namespace BRel
variable {H : Type*}
end BRel

end OneWayLiveness

end OAI

-- ---- platform node ----
open OAI OAI.OneWayLiveness OAI.OneWayLiveness.RectangleFrame


theorem solution : type_of% @_root_.OAI.OneWayLiveness.RectangleFrame.rel_mul := @_root_.OAI.OneWayLiveness.RectangleFrame.rel_mul
