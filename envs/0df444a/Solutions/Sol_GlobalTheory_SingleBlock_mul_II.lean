-- Prove2me | solution 1 for GlobalTheory.SingleBlock.mul_II
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:51:40.207797+00:00
-- url     : https://prove2.me/submissions/b03a4377-4573-48a8-8da6-a137ffa4b0ee

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
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
variable {F : Type} [Field F] {r t : ℕ} {O : Subring F} {ϖ : F} {P : Subgroup (GL (Fin r) F)}
namespace GlobalTheory.SingleBlock
theorem _root_.solution {l m n : ℕ} {A : Matrix (Fin l) (Fin m) F} (hA : ∀ i j, A i j ∈ O)
    {y : Matrix (Fin m) (Fin n) F} (hy : y ∈ IIset O ϖ) : A * y ∈ IIset O ϖ := by
  intro i j
  choose o ho he using hy
  refine ⟨∑ k, A i k * o k j, Subring.sum_mem _ (fun k _ => O.mul_mem (hA i k) (ho k j)), ?_⟩
  simp only [Matrix.mul_apply, he, Finset.mul_sum, mul_left_comm]
end GlobalTheory.SingleBlock
