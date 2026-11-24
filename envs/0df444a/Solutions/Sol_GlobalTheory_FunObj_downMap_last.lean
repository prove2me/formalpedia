-- Prove2me | solution 1 for GlobalTheory.FunObj.downMap_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:48:32.415181+00:00
-- url     : https://prove2.me/submissions/ec4bc8dc-6647-4817-a034-4d91748e6447

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
variable (hs : 1 ≤ G.s)
namespace GlobalTheory.FunObj
theorem _root_.solution (hm : 0 < G.m) (x : ColArgs G) (e : Vars G) : downMap hs x e (G.m - 1) = lastMap hs hm x := by
  rw [downMap, dif_neg (lt_irrefl _), dif_pos (by omega)]; rfl
end GlobalTheory.FunObj
