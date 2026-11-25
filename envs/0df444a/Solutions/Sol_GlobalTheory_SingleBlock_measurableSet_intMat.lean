-- Prove2me | solution 1 for GlobalTheory.SingleBlock.measurableSet_intMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:53:33.928963+00:00
-- url     : https://prove2.me/submissions/6b856a85-8b38-4fb2-90ab-bf4e4698db39

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_iiset_eq
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_meas_ii
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {r t : ℕ}
  {O : Subring F} {ϖ : F} {P : Subgroup (GL (Fin r) F)}
variable [MeasurableSpace F] [BorelSpace F]
namespace GlobalTheory.SingleBlock
theorem _root_.solution (hO : IsOpen (O : Set F)) (n a : ℕ) :
    MeasurableSet (intMat O n a) := by
  have := Vol.meas_ii O hO 1 one_ne_zero n a
  rw [Vol.iiset_eq O 1 one_ne_zero] at this
  simpa [intMat] using this
end GlobalTheory.SingleBlock
