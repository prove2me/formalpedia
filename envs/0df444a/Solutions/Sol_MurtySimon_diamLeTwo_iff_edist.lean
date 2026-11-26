-- Prove2me | solution 1 for MurtySimon.diamLeTwo_iff_edist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:48:31.819803+00:00
-- url     : https://prove2.me/submissions/f75dcb16-813d-4d73-8832-d5068112d47f

module
public import Mathlib
public import Definitions.Def_MurtySimon_Defs

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open SimpleGraph
variable {V : Type*}
namespace MurtySimon
theorem _root_.solution (G : SimpleGraph V) : DiamLeTwo G ↔ ∀ u v, G.edist u v ≤ 2 := by
  constructor
  · intro h u v
    by_cases huv : u = v
    · subst huv; simp
    rcases h u v huv with hadj | ⟨w, h1, h2⟩
    · calc G.edist u v ≤ (Walk.cons hadj Walk.nil).length := G.edist_le _
        _ ≤ 2 := by simp
    · calc G.edist u v ≤ (Walk.cons h1 (Walk.cons h2 Walk.nil)).length := G.edist_le _
        _ = 2 := by simp
  · intro h u v huv
    have hne : G.edist u v ≠ ⊤ := ne_top_of_le_ne_top (by decide) (h u v)
    obtain ⟨p, hp⟩ := (reachable_of_edist_ne_top hne).exists_walk_length_eq_edist
    have hlen : p.length ≤ 2 := by
      have := h u v
      rw [← hp] at this
      exact_mod_cast this
    rcases p with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, p⟩⟩⟩
    · exact absurd rfl huv
    · exact Or.inl h1
    · exact Or.inr ⟨_, h1, h2⟩
    · simp at hlen
end MurtySimon
