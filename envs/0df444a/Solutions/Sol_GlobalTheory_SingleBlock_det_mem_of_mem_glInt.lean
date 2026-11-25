-- Prove2me | solution 1 for GlobalTheory.SingleBlock.det_mem_of_mem_glInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:57:01.16983+00:00
-- url     : https://prove2.me/submissions/30af8477-9ab1-4f02-b9e3-07fdc1b8196b

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
theorem _root_.solution {O : Subring F} {n : Type} [Fintype n] [DecidableEq n] {g : GL n F}
    (hg : g ∈ glInt O n) : ((GeneralLinearGroup.det g : Fˣ) : F) ∈ O := by
  obtain ⟨g0, rfl⟩ := hg
  have : ((GeneralLinearGroup.det (GeneralLinearGroup.map (n := n) O.subtype g0) : Fˣ) : F) =
      O.subtype (g0 : Matrix n n O).det := by
    rw [RingHom.map_det]; rfl
  rw [this]; exact Subtype.coe_prop _
end GlobalTheory.SingleBlock
