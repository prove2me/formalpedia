-- Prove2me | solution 1 for MooreGraphs.no_triangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:15:48.639701+00:00
-- url     : https://prove2.me/submissions/d1908d11-c36d-4c1c-ba40-f1ac34b823b0

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
theorem _root_.solution (hgirth : 5 ≤ G.egirth) {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hca : G.Adj c a) : False := by
  have hc : (Walk.cons hab (Walk.cons hbc (Walk.cons hca Walk.nil))).IsCycle := by
    rw [Walk.cons_isCycle_iff]
    simp [Walk.cons_isPath_iff, hab.ne, hbc.ne, hca.ne, hab.ne.symm, hca.ne.symm]
  have := le_egirth.1 hgirth a _ hc
  simp at this
  norm_num at this
end MooreGraphs
