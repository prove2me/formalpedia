-- Prove2me | solution 1 for MurtySimon.two_le_edist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:22:00.728277+00:00
-- url     : https://prove2.me/submissions/65131770-697b-418c-9c32-4a5d795fc735

module
public import Definitions.Def_MurtySimon_Equality
public import Definitions.Def_MurtySimon_Main

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]
namespace MurtySimon
theorem _root_.solution {W : Type*} {H : SimpleGraph W} {u v : W} (hne : u ≠ v) (hn : ¬ H.Adj u v) :
    2 ≤ H.edist u v := by
  by_contra h
  push Not at h
  have hne' : H.edist u v ≠ ⊤ := ne_top_of_lt h
  obtain ⟨p, hp⟩ := (reachable_of_edist_ne_top hne').exists_walk_length_eq_edist
  have hlen : p.length < 2 := by rw [← hp] at h; exact_mod_cast h
  rcases p with _ | ⟨h1, _ | ⟨h2, p⟩⟩
  · exact hne rfl
  · exact hn h1
  · simp at hlen
end MurtySimon
