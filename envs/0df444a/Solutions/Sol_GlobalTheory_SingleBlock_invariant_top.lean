-- Prove2me | solution 1 for GlobalTheory.SingleBlock.invariant_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:58:34.091788+00:00
-- url     : https://prove2.me/submissions/e614b2fd-9426-4da3-bd77-08d25e6db1ba

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Theorems.Thm_P2M_GlobalTheory_SingleBlock_measurable_toRows__1516c29dbd57
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
    (B : Set (Matrix (Fin t) (Fin r) F)) :
    ((ν.restrict (toRows₂ ⁻¹' B)).map toRows₁).IsAddLeftInvariant := by
  have := measurableAdd_rows (F := F) (r := r) (t := t)
  refine ⟨fun g => Measure.ext fun A hA => ?_⟩
  have hg := Vol.meas_add r r g
  rw [Measure.map_apply hg hA, Measure.map_apply measurable_toRows₁ (hg hA),
    Measure.map_apply measurable_toRows₁ hA, Measure.restrict_apply (measurable_toRows₁ (hg hA)),
    Measure.restrict_apply (measurable_toRows₁ hA),
    ← measure_preimage_add ν (fromRows g 0) (_ ⁻¹' A ∩ _)]
  congr 1
  ext x
  have e1 : toRows₁ (fromRows g 0 + x) = g + toRows₁ x := by ext i j; simp
  have e2 : toRows₂ (fromRows g 0 + x) = toRows₂ x := by ext i j; simp
  simp only [Set.mem_inter_iff, Set.mem_preimage, e1, e2]
end GlobalTheory.SingleBlock
