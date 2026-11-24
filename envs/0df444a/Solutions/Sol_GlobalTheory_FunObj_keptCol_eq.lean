-- Prove2me | solution 1 for GlobalTheory.FunObj.keptCol_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:52:44.831026+00:00
-- url     : https://prove2.me/submissions/cdff221d-04b8-4600-b560-18e51d77dcb9

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
theorem _root_.solution (w : KeptVars G) (j : Fin (G.m - 1)) (hj : Even (G.m - 2 - j)) (r : Fin (topRank G (j + 1))) :
    keptCol w j r = w j ⟨(.inl r, .inr ⟨(G.m - 2 - j) / 2, by omega⟩), hj, rfl⟩ := dif_pos _
end GlobalTheory.FunObj
