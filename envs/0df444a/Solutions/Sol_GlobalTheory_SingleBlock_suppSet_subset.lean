-- Prove2me | solution 1 for GlobalTheory.SingleBlock.suppSet_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:52:38.853772+00:00
-- url     : https://prove2.me/submissions/21baeb8b-5bc7-41c8-a077-bf18cf4adeaa

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
variable {F : Type} [Field F] {r t : ℕ} {O : Subring F} {ϖ : F} {P : Subgroup (GL (Fin r) F)}
namespace GlobalTheory.SingleBlock
theorem _root_.solution (hϖ : ϖ ∈ O) (hP : P ≤ GLint O r) :
    suppSet t O ϖ P ⊆ intMatrices O (Fin r ⊕ Fin t) (Fin r) := by
  rintro x ⟨⟨p, hp, ep⟩, h2⟩ (i | i) j
  · have e2 : (p : Matrix (Fin r) (Fin r) F) i j = x (Sum.inl i) j := congrFun (congrFun ep i) j
    rw [← e2]; exact (hP hp).1 i j
  · obtain ⟨o, ho, e⟩ := h2 i j
    have e2 : x (Sum.inr i) j = ϖ * o := e
    rw [e2]; exact O.mul_mem hϖ ho
end GlobalTheory.SingleBlock
