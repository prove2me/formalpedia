-- Prove2me | solution 1 for MooreGraphs.no_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:15:51.390475+00:00
-- url     : https://prove2.me/submissions/ab5927e1-fa2f-4ec9-8cb2-872f7c5775b1

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
theorem _root_.solution (hgirth : 5 ≤ G.egirth) {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hda : G.Adj d a) (hac : a ≠ c) (hbd : b ≠ d) : False := by
  have hc : (Walk.cons hab (Walk.cons hbc (Walk.cons hcd (Walk.cons hda Walk.nil)))).IsCycle := by
    rw [Walk.cons_isCycle_iff]
    simp [Walk.cons_isPath_iff, hab.ne, hbc.ne, hcd.ne, hda.ne, hab.ne.symm, hda.ne.symm, hac,
      hbd, hac.symm]
  have := le_egirth.1 hgirth a _ hc
  simp at this
  norm_num at this
end MooreGraphs
