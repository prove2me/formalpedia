-- Prove2me | solution 1 for GlobalTheory.SingleBlock.det_inv_mem_of_mem_glInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:02:58.0728+00:00
-- url     : https://prove2.me/submissions/7900814a-1e5c-4330-b077-bd0987d6a6bf

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FromBlocksMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
import Theorems.Thm_GlobalTheory_SingleBlock_det_mem_of_mem_glInt

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
theorem _root_.solution {O : Subring F} {n : Type} [Fintype n] [DecidableEq n]
    {g : GL n F} (hg : g ∈ glInt O n) : (((GeneralLinearGroup.det g)⁻¹ : Fˣ) : F) ∈ O := by
  rw [← map_inv]; exact det_mem_of_mem_glInt (inv_mem hg)
end GlobalTheory.SingleBlock
