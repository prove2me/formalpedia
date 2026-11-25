-- Prove2me | solution 1 for GlobalTheory.SingleBlock.measurableAdd_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:51:36.319805+00:00
-- url     : https://prove2.me/submissions/6452932d-96ec-4035-b0ef-d0670e251801

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {r t : ℕ}
  {O : Subring F} {ϖ : F} {P : Subgroup (GL (Fin r) F)}
variable [MeasurableSpace F] [BorelSpace F]
namespace GlobalTheory.SingleBlock
theorem _root_.solution : MeasurableAdd (Matrix (Fin r ⊕ Fin t) (Fin r) F) :=
  inferInstanceAs (MeasurableAdd (Fin r ⊕ Fin t → Fin r → F))
end GlobalTheory.SingleBlock
