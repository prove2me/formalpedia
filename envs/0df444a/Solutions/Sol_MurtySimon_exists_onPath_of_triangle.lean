-- Prove2me | solution 1 for MurtySimon.exists_onPath_of_triangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:55:13.855504+00:00
-- url     : https://prove2.me/submissions/ae556856-2261-4c1a-8e33-c9f658dcd551

module
public import Definitions.Def_MurtySimon_Defs
public import Definitions.Def_MurtySimon_Basic
public import Theorems.Thm_MurtySimon_IsMid_symm
public import Theorems.Thm_MurtySimon_OnPath_ne
public import Theorems.Thm_MurtySimon_onPath_iff

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
variable {G}
namespace MurtySimon
theorem _root_.solution (hG : IsCritical G) {x y w : V} (hxy : G.Adj x y)
    (hxw : G.Adj x w) (hwy : G.Adj w y) : ∃ f, OnPath G s(x, y) f := by
  have hnd := hG.2 s(x, y) hxy
  have hwx : w ≠ x := hxw.ne'
  have hwy' : w ≠ y := hwy.ne
  -- an edge through `w` is not `xy`
  have hw : ∀ p, s(p, w) ≠ s(x, y) := by
    intro p hp
    have : w ∈ s(x, y) := hp ▸ Sym2.mem_mk_right p w
    rcases Sym2.mem_iff.1 this with h | h
    · exact hwx h
    · exact hwy' h
  have hw' : ∀ p, s(w, p) ≠ s(x, y) := fun p => by rw [Sym2.eq_swap]; exact hw p
  have hdel : ∀ p q, (G.deleteEdges {s(x, y)}).Adj p q ↔ G.Adj p q ∧ s(p, q) ≠ s(x, y) := by
    intro p q; simp
  unfold DiamLeTwo at hnd
  push Not at hnd
  obtain ⟨a, b, hab, hnab, hcom⟩ := hnd
  simp only [hdel, not_and, not_not] at hnab hcom
  by_cases hadj : G.Adj a b
  · have he : s(a, b) = s(x, y) := hnab hadj
    exfalso
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hw' b (hcom w ⟨hxw, hw a⟩ hwy)
    · exact hw' b (hcom w ⟨hwy.symm, hw a⟩ hxw.symm)
  · obtain hab' | ⟨u, hau, hub⟩ := hG.1 a b hab
    · exact absurd hab' hadj
    -- every common neighbour uses the edge `xy`
    have huse : ∀ z, G.Adj a z → G.Adj z b → s(a, z) = s(x, y) ∨ s(z, b) = s(x, y) := by
      intro z hz1 hz2
      by_contra hcon
      push Not at hcon
      exact hcon.2 (hcom z ⟨hz1, hcon.1⟩ hz2)
    have huniq : ∀ z, G.Adj a z → G.Adj z b → z = u := by
      intro z hz1 hz2
      rcases huse z hz1 hz2 with h1 | h1 <;> rcases huse u hau hub with h2 | h2
      · exact Sym2.congr_right.1 (h1.trans h2.symm)
      · rcases Sym2.eq_iff.1 (h1.trans h2.symm) with ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd (h ▸ hau) (G.loopless.irrefl u)
        · exact h
      · rcases Sym2.eq_iff.1 (h1.trans h2.symm) with ⟨h, -⟩ | ⟨h, -⟩
        · exact absurd h.symm (hz1.ne)
        · exact h
      · exact Sym2.congr_left.1 (h1.trans h2.symm)
    have hm : IsMid G a b u := ⟨hab, hadj, hau, hub, huniq⟩
    refine ⟨s(a, b), (onPath_iff hm).2 ?_⟩
    rcases huse u hau hub with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
end MurtySimon
