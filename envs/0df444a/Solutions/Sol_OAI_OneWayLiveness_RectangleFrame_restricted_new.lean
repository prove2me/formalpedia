-- Prove2me | solution 1 for OAI.OneWayLiveness.RectangleFrame.restricted_new
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:56:25.651757+00:00
-- url     : https://prove2.me/submissions/f1788fb2-a249-414d-8fd3-c256b37c2e40

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Relations.lean:L255-L272
-- (upload_full_project.md Phase 4): solution for node OAI.OneWayLiveness.RectangleFrame.restricted_new. The node keeps its source
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
lemma restricted_new (E : Set (I × J)) (K : Set H)
    (hK : ∀ x ∈ K, x ≠ F.hub)
    (hE : ∀ p ∈ E, F.left p.1 ∉ K ∨ F.right p.2 ∉ K)
    (i : I) (j : J) (hi : F.left i ∈ K) (hj : F.right j ∈ K) :
    let u : K := ⟨F.left i,hi⟩
    let v : K := ⟨F.right j,hj⟩
    ∀ x y : K, (F.rel (insert (i,j) E)).holds x.val y.val ↔ (BRel.addEdge u v).holds x y := by
  intro u v x y
  simp only [rel_holds, BRel.addEdge_holds]
  constructor
  · rintro (⟨hxy, _⟩ | ⟨p, hp, hx, hy⟩)
    · exact Or.inl (Subtype.ext hxy)
    · rcases hp with rfl | hp
      · exact Or.inr ⟨Subtype.ext hx, Subtype.ext hy⟩
      · exact ((hE p hp).elim (fun h => h (hx ▸ x.property)) (fun h => h (hy ▸ y.property))).elim
  · rintro (rfl | ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, hK x.val x.property⟩
    · exact Or.inr ⟨(i,j), Or.inl rfl, rfl, rfl⟩
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


theorem solution : type_of% @_root_.OAI.OneWayLiveness.RectangleFrame.restricted_new := @_root_.OAI.OneWayLiveness.RectangleFrame.restricted_new
