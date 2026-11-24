-- Prove2me | solution 1 for GlobalTheory.FunObj.OneCosetProof.stepPt_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:08:42.561378+00:00
-- url     : https://prove2.me/submissions/4ab343b8-2dc8-4989-af25-b57b2c4f652b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCosetOfIsTensor
import Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_stepPt_add

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
theorem _root_.solution (x : ColArgs G) (e : Vars G) (Y : Shift G)
    (hY : ∀ j r s, ¬ Free ((G.m - 2 - j.val) / 2 + 1) (r, s) → Y j r s = 0) (j : Fin (G.m - 1)) :
    stepPt (x j) ((e + Y.vars) j) = stepPt (x j) (e j) + Y j := by
  exact stepPt_add (x j) (e j) (Y j) (hY j)
end GlobalTheory.FunObj.OneCosetProof
