-- Prove2me | solution 1 for OAI.OneWayLiveness.permutation_single_entrance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:34:58.92854+00:00
-- url     : https://prove2.me/submissions/b5ba8f1b-b5d9-4533-8e38-724ae3f1926a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Tours.lean:L7-L23
-- (upload_full_project.md Phase 4): solution for node OAI.OneWayLiveness.permutation_single_entrance. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours

-- ---- from OAI.Combinatorics.Automata.Tours ----
namespace OAI

namespace OneWayLiveness

/-- A finite permutation cannot leave a set without later re-entering it.
When there is only one entrance, its entrance dart lies on the same tour. -/
lemma permutation_single_entrance {D : Type*} [Finite D] (τ : Equiv.Perm D)
    (U : Set D) (a b : D) (ha : a ∈ U) (ha' : τ a ∉ U)
    (hin : ∀ d, d ∉ U → τ d ∈ U → d = b) : τ.SameCycle a b := by
  classical
  by_contra hb
  let S : Set D := {d | τ.SameCycle a d ∧ d ∉ U}
  have hm : Set.MapsTo τ S S := by
    rintro d ⟨hd, hdu⟩
    refine ⟨by simpa using hd, ?_⟩
    intro hτd
    exact hb (hin d hdu hτd ▸ hd)
  have hbij := (Set.toFinite S).injOn_iff_bijOn_of_mapsTo hm |>.mp τ.injective.injOn
  obtain ⟨c, hc, he⟩ := hbij.surjOn ⟨by simpa using (Equiv.Perm.SameCycle.refl τ a), ha'⟩
  have hca : c = a := τ.injective he
  exact hc.2 (hca ▸ ha)

namespace FunctionalEdges
variable {V E : Type*} (G : FunctionalEdges V E)
namespace Rotation
variable {G} (R : G.Rotation)
end Rotation
end FunctionalEdges
end OneWayLiveness

end OAI

-- ---- platform node ----
open OAI OAI.OneWayLiveness


theorem solution : type_of% @_root_.OAI.OneWayLiveness.permutation_single_entrance := @_root_.OAI.OneWayLiveness.permutation_single_entrance
