-- Prove2me | solution 1 for GlobalTheory.SingleBlock.invariant_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:58:33.44252+00:00
-- url     : https://prove2.me/submissions/bec50264-f00d-4406-b914-0d10f94c6d6c

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Theorems.Thm_P2M_GlobalTheory_SingleBlock_measurable_toRows__be0362a1a7c9
import Theorems.Thm_GlobalTheory_SingleBlock_measurableAdd_rows
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_meas_add
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
theorem _root_.solution (ν : Measure (Matrix (Fin r ⊕ Fin t) (Fin r) F)) [ν.IsAddLeftInvariant]
    (A : Set (Matrix (Fin r) (Fin r) F)) :
    ((ν.restrict (toRows₁ ⁻¹' A)).map toRows₂).IsAddLeftInvariant := by
  have := measurableAdd_rows (F := F) (r := r) (t := t)
  refine ⟨fun g => Measure.ext fun B hB => ?_⟩
  have hg := Vol.meas_add t r g
  rw [Measure.map_apply hg hB, Measure.map_apply measurable_toRows₂ (hg hB),
    Measure.map_apply measurable_toRows₂ hB, Measure.restrict_apply (measurable_toRows₂ (hg hB)),
    Measure.restrict_apply (measurable_toRows₂ hB),
    ← measure_preimage_add ν (fromRows 0 g) (_ ⁻¹' B ∩ _)]
  congr 1
  ext x
  have e1 : toRows₁ (fromRows 0 g + x) = toRows₁ x := by ext i j; simp
  have e2 : toRows₂ (fromRows 0 g + x) = g + toRows₂ x := by ext i j; simp
  simp only [Set.mem_inter_iff, Set.mem_preimage, e1, e2]
end GlobalTheory.SingleBlock
