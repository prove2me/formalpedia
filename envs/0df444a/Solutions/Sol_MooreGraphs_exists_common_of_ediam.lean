-- Prove2me | solution 1 for MooreGraphs.exists_common_of_ediam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:15:46.621199+00:00
-- url     : https://prove2.me/submissions/652fd601-d9d0-4dc9-8e5b-c4380d6251ee

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphsAux

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Matrix
open MooreGraphs
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
omit [Fintype V] [DecidableRel G.Adj]
namespace MooreGraphs
theorem _root_.solution {u v : V} (hdiam : G.ediam ≤ 2) (huv : u ≠ v)
    (hadj : ¬G.Adj u v) : ∃ w, G.Adj u w ∧ G.Adj w v := by
  by_contra h
  have hempty : G.commonNeighbors u v = ∅ := by
    ext w
    simp only [mem_commonNeighbors, Set.mem_empty_iff_false, iff_false]
    exact fun ⟨h1, h2⟩ => h ⟨w, h1, h2.symm⟩
  have := (two_lt_edist_iff (G := G)).2 ⟨huv, hadj, hempty⟩
  exact absurd (edist_le_ediam.trans hdiam) (not_le.2 this)
end MooreGraphs
