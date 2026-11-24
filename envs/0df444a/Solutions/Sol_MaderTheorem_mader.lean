-- Prove2me | solution 1 for MaderTheorem.mader
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:59:25.004069+00:00
-- url     : https://prove2.me/submissions/a8b8f9af-b71b-40cf-8a52-85e02bc8394d

module
public import Mathlib
public import Definitions.Def_MaderLib_Mader
public import Definitions.Def_MaderLib_Solution
public import Theorems.Thm_Mader_mader


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open MaderTheorem
variable {V : Type*}
namespace MaderTheorem
theorem _root_.solution [Fintype V] [Nonempty V] (G : SimpleGraph V) {k : ℕ} (hk : 1 ≤ k)
    (hd : 4 * k * Fintype.card V ≤ 2 * G.edgeSet.ncard) :
    ∃ S : Finset V, IsKConnected (G.induce (S : Set V)) (k + 1) ∧
      (G.edgeSet.ncard : ℝ) / Fintype.card V - k <
        ((G.induce (S : Set V)).edgeSet.ncard : ℝ) / S.card :=
  Mader.mader G hk hd
end MaderTheorem
