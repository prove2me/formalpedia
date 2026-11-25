-- Prove2me | solution 1 for GlobalTheory.SingleBlock.II_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:51:35.681817+00:00
-- url     : https://prove2.me/submissions/86c6b0a5-ae51-4de1-8a2f-1e0c57745e60

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
theorem _root_.solution {m n : ℕ} {y z : Matrix (Fin m) (Fin n) F} (hy : y ∈ IIset O ϖ)
    (hz : z ∈ IIset O ϖ) : y + z ∈ IIset O ϖ := by
  intro i j
  obtain ⟨a, ha, e⟩ := hy i j
  obtain ⟨b, hb, e'⟩ := hz i j
  exact ⟨a + b, O.add_mem ha hb, by rw [Matrix.add_apply, e, e', mul_add]⟩
end GlobalTheory.SingleBlock
