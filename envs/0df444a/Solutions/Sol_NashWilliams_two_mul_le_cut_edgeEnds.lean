-- Prove2me | solution 1 for NashWilliams.two_mul_le_cut_edgeEnds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:29:37.949797+00:00
-- url     : https://prove2.me/submissions/d1d51e9b-769e-425c-93ee-6062ffec004e

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Orientation
public import Definitions.Def_NashWilliamsLib_Defs
public import Theorems.Thm_NashWilliams_edgeEnds_eq_or

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V : Type*} (G : SimpleGraph V)
namespace NashWilliams
theorem _root_.solution [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {k : ℕ}
    (hG : G.IsEdgeConnected (2 * k)) {S : Finset V}
    (hne : S.Nonempty) (hneT : S ≠ Finset.univ) : 2 * k ≤ cut (edgeEnds G) S := by
  by_contra hlt
  push Not at hlt
  set C : Finset (Sym2 V) := (Finset.univ.filter fun e : G.edgeSet =>
    ((edgeEnds G e).1 ∈ S) ≠ ((edgeEnds G e).2 ∈ S)).image Subtype.val with hC
  have hCcard : C.card < 2 * k := lt_of_le_of_lt card_image_le hlt
  obtain ⟨u, hu⟩ := hne
  obtain ⟨v, hv⟩ : ∃ v, v ∉ S := by
    by_contra! h
    exact hneT (eq_univ_of_forall h)
  have hr : (G.deleteEdges (C : Set (Sym2 V))).Reachable u v := hG u v (by
    rw [Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hCcard)
  obtain ⟨p⟩ := hr
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart (S : Set V) (by simpa using hu)
    (by simpa using hv)
  have hadj := d.adj
  rw [SimpleGraph.deleteEdges_adj] at hadj
  obtain ⟨hadj, hnot⟩ := hadj
  apply hnot
  have hd1' : d.fst ∈ S := by simpa using hd1
  have hd2' : d.snd ∉ S := by simpa using hd2
  refine mem_image.2 ⟨⟨s(d.fst, d.snd), hadj⟩, mem_filter.2 ⟨mem_univ _, ?_⟩, rfl⟩
  rcases edgeEnds_eq_or G (e := ⟨s(d.fst, d.snd), hadj⟩) rfl with h | h <;> rw [h] <;>
    simp [hd1', hd2']
end NashWilliams
