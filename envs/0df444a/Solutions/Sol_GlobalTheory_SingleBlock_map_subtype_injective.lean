-- Prove2me | solution 1 for GlobalTheory.SingleBlock.map_subtype_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:56:51.368682+00:00
-- url     : https://prove2.me/submissions/ddd73552-7e54-42ef-bb86-fcfe197ef56b

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FromBlocksMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_T2SpaceIsNonarchimedeanLocalFieldSingleBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate ValuativeRel Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
variable {F : Type} [Field F]
namespace GlobalTheory.SingleBlock
theorem _root_.solution (O : Subring F) (n : Type) [Fintype n] [DecidableEq n] :
    Function.Injective (GeneralLinearGroup.map (n := n) O.subtype) := by
  intro g h e
  apply Units.ext
  ext a b
  exact congrArg (fun x : GL n F => (x : Matrix n n F) a b) e
end GlobalTheory.SingleBlock
