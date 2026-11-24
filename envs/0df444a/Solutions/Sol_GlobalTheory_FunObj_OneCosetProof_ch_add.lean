-- Prove2me | solution 1 for GlobalTheory.FunObj.OneCosetProof.ch_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:47:16.711052+00:00
-- url     : https://prove2.me/submissions/4784c0e8-62a0-4311-889b-3a1a73d40526

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
namespace GlobalTheory.FunObj.OneCosetProof
theorem _root_.solution {n n' : Type} {c : ℕ} (X Y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : ch (X + Y) = ch X + ch Y := by
  simp only [ch, Matrix.add_apply]
  exact Finset.sum_add_distrib
end GlobalTheory.FunObj.OneCosetProof
