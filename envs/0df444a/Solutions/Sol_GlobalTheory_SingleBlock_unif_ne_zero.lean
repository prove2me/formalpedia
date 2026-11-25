-- Prove2me | solution 1 for GlobalTheory.SingleBlock.unif_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:57:02.065803+00:00
-- url     : https://prove2.me/submissions/4403c00b-e99d-41cf-87fc-bd1172cce36c

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
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {r t : ℕ} {ϖ : 𝒪[F]}
namespace GlobalTheory.SingleBlock
theorem _root_.solution (hϖ : Irreducible ϖ) : (ϖ : F) ≠ 0 :=
  fun h => hϖ.ne_zero (Subtype.ext h)
end GlobalTheory.SingleBlock
