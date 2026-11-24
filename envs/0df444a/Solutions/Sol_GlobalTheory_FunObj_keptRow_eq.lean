-- Prove2me | solution 1 for GlobalTheory.FunObj.keptRow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:52:45.835131+00:00
-- url     : https://prove2.me/submissions/41bc4e91-d406-491f-a479-a67cfd54d8a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] (G : Grid k)
variable {G}
namespace GlobalTheory.FunObj
theorem _root_.solution (x : ColArgs G) (w : KeptVars G) (j : Fin (G.m - 1)) (hj : Odd (G.m - 2 - j))
    (s : Fin (topRank G j)) : keptRow x w j s =
      w j ⟨(.inr ⟨(G.m - 2 - j) / 2, by have := hj.pos; omega⟩, .inl s), hj, rfl⟩ := by
  rw [keptRow, dif_pos j.2, Finset.sum_eq_single ⟨(G.m - 2 - j) / 2, by have := hj.pos; omega⟩, if_pos rfl]
  · exact dif_pos _
  · exact fun l _ hl => if_neg fun h => hl (Fin.ext h)
  · simp
end GlobalTheory.FunObj
