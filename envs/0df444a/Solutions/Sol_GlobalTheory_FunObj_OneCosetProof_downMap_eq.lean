-- Prove2me | solution 1 for GlobalTheory.FunObj.OneCosetProof.downMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:49.293802+00:00
-- url     : https://prove2.me/submissions/1d3e3721-3ced-4e98-be42-c18ddbe9367f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCosetOfIsTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.OneCosetProof
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type} [Field k]
variable {G : Grid k}
namespace GlobalTheory.FunObj.OneCosetProof
theorem _root_.solution (hs : 1 ≤ G.s) (x : ColArgs G) (e : Vars G) (j : Fin (G.m - 1)) : downMap hs x e j =
    (stepPt (x j) (e j)).reindex (frame (tgt_eq hs j)) (frame (src_eq hs j)) := by
  unfold downMap
  rw [dif_pos j.isLt]
end GlobalTheory.FunObj.OneCosetProof
