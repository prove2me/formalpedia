-- Prove2me | solution 1 for OAI.OneWayLiveness.FunctionalEdges.Rotation.edge_sameCycle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:36:23.312291+00:00
-- url     : https://prove2.me/submissions/07295229-beb3-47a1-afeb-70fc4b51363e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Tours.lean:L150-L168
-- (upload_full_project.md Phase 4): solution for node OAI.OneWayLiveness.FunctionalEdges.Rotation.edge_sameCycle. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Theorems.Thm_OAI_OneWayLiveness_permutation_single_entrance

-- ---- from OAI.Combinatorics.Automata.Tours ----
namespace OAI

namespace OneWayLiveness

namespace FunctionalEdges
variable {V E : Type*} (G : FunctionalEdges V E)
lemma deterministic {v w z : V} (h : G.Step v w) (h' : G.Step v z) : w = z := by
  obtain ⟨e, hs, hd⟩ := h
  obtain ⟨e', hs', hd'⟩ := h'
  have he : e = e' := G.src_injective (hs.trans hs'.symm)
  exact hd.symm.trans (he ▸ hd')

lemma reach_of_terminal {t v : V} (ht : ∀ e, G.src e ≠ t) (h : G.Reach t v) : t = v := by
  rcases h.cases_head with h | ⟨w, ⟨e, he, _⟩, _⟩
  · exact h
  · exact (ht e he).elim

lemma edge_cut {e f : E} (hne : f ≠ e) :
    G.Reach (G.src f) (G.src e) ↔ G.Reach (G.dst f) (G.src e) := by
  constructor
  · intro h
    rcases h.cases_head with heq | ⟨v, hfv, hve⟩
    · exact (hne (G.src_injective heq)).elim
    · have heq : G.dst f = v := G.deterministic ⟨f, rfl, rfl⟩ hfv
      exact heq ▸ hve
  · exact fun h => h.head ⟨f, rfl, rfl⟩

lemma edge_not_return {t : V} (ht : ∀ e, G.src e ≠ t) (e : E)
    (h : G.Reach (G.src e) t) : ¬ G.Reach (G.dst e) (G.src e) := by
  intro he
  have closed {v w : V} (hv : G.Reach v (G.src e)) (hvw : G.Step v w) :
      G.Reach w (G.src e) := by
    rcases hv.cases_head with rfl | ⟨z, hvz, hze⟩
    · have this := G.deterministic hvw (show G.Step (G.src e) (G.dst e) from ⟨e, rfl, rfl⟩)
      simpa [this] using he
    · exact G.deterministic hvw hvz ▸ hze
  have hh : G.Reach t (G.src e) := by
    clear ht
    induction h with
    | refl => exact .refl
    | tail _ hvw ih => exact closed ih hvw
  exact ht e (G.reach_of_terminal ht hh).symm

namespace Rotation
variable {G} (R : G.Rotation)
lemma tour_vertex (d : E × Bool) : G.vertex (R.tour d) = G.vertex (G.flip d) := R.vertex_eq _

lemma edge_sameCycle [Finite E] {t : V} (ht : ∀ e, G.src e ≠ t) (e : E)
    (h : G.Reach (G.src e) t) : R.tour.SameCycle (e, false) (e, true) := by
  let U : Set (E × Bool) := {d | G.Reach (G.vertex d) (G.src e)}
  have hae : (e, false) ∈ U := Relation.ReflTransGen.refl
  have hae' : R.tour (e, false) ∉ U := by
    change ¬ G.Reach (G.vertex (R.tour (e, false))) (G.src e)
    rw [R.tour_vertex]
    exact G.edge_not_return ht e h
  apply permutation_single_entrance R.tour U (e, false) (e, true) hae hae'
  rintro ⟨f, b⟩ ho hi
  change G.Reach (G.vertex (R.tour (f,b))) (G.src e) at hi
  rw [R.tour_vertex] at hi
  cases b with
  | false => exact (ho (hi.head ⟨f, rfl, rfl⟩)).elim
  | true =>
    have hfe : f = e := by
      by_contra hne
      exact ho ((G.edge_cut hne).mp hi)
    exact Prod.ext hfe rfl

end Rotation
end FunctionalEdges
end OneWayLiveness

end OAI

-- ---- platform node ----
open OAI OAI.OneWayLiveness OAI.OneWayLiveness.FunctionalEdges OAI.OneWayLiveness.FunctionalEdges.Rotation


theorem solution : type_of% @_root_.OAI.OneWayLiveness.FunctionalEdges.Rotation.edge_sameCycle := @_root_.OAI.OneWayLiveness.FunctionalEdges.Rotation.edge_sameCycle
