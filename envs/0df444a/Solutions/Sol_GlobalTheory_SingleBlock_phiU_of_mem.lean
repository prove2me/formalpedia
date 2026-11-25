-- Prove2me | solution 1 for GlobalTheory.SingleBlock.phiU_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:51:36.396105+00:00
-- url     : https://prove2.me/submissions/e2bdcd0a-b97f-4ffa-a4f0-80fffd8aee3d

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_LemmaU_choose_eq


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
theorem _root_.solution (ρ : P →* ℂˣ) {x : Matrix (Fin r ⊕ Fin t) (Fin r) F} (k : P)
    (hk : ((k : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = toRows₁ x)
    (h2 : toRows₂ x ∈ IIset O ϖ) : phiU O ϖ P ρ x = ((ρ k : ℂˣ) : ℂ) := by
  have h1 : (∃ k : P, ((k : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = toRows₁ x) ∧
      toRows₂ x ∈ IIset O ϖ := ⟨⟨k, hk⟩, h2⟩
  unfold phiU
  rw [dif_pos h1, LemmaU.choose_eq h1.1 k hk]
end GlobalTheory.SingleBlock
