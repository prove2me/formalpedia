-- Prove2me | solution 1 for GlobalTheory.LocFlat.SuppColProof.det_colE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:39:40.745136+00:00
-- url     : https://prove2.me/submissions/35bacad4-70a6-48ff-b2ab-b5fe12ec54c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnMapEqRootExchangeOperatorTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnSupportOfOneIndexAtSymPosition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.SuppColProof
namespace GlobalTheory.LocFlat.SuppColProof
theorem _root_.solution {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (c p : ℕ) (β : n → k) :
    Matrix.GeneralLinearGroup.det (colE c p β) = 1 := by
  ext
  simp [colE, upU]
end GlobalTheory.LocFlat.SuppColProof
