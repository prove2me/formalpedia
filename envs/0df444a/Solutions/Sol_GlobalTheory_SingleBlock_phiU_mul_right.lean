-- Prove2me | solution 1 for GlobalTheory.SingleBlock.phiU_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:56.764256+00:00
-- url     : https://prove2.me/submissions/793e883c-10f3-4b64-9b5f-44c34596f76e

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Theorems.Thm_GlobalTheory_SingleBlock_phiU_of_notMem
import Theorems.Thm_GlobalTheory_SingleBlock_mul_right_mem

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
theorem _root_.solution (hP : P ≤ GLint O r) (ρ : P →* ℂˣ) (g : P)
    (x : Matrix (Fin r ⊕ Fin t) (Fin r) F) :
    phiU O ϖ P ρ (x * ((g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) =
      ((ρ g : ℂˣ) : ℂ) * phiU O ϖ P ρ x := by
  by_cases hx : x ∈ suppSet t O ϖ P
  · exact (mul_right_mem hP ρ g hx).2
  · rw [phiU_of_notMem ρ hx, mul_zero, phiU_of_notMem]
    intro h
    have := (mul_right_mem hP ρ g⁻¹ h).1
    rw [Matrix.mul_assoc, ← Units.val_mul, Subgroup.coe_inv, mul_inv_cancel, Units.val_one,
      Matrix.mul_one] at this
    exact hx this
end GlobalTheory.SingleBlock
