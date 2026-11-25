-- Prove2me | solution 1 for GlobalTheory.SingleBlock.phiU_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:51:31.009453+00:00
-- url     : https://prove2.me/submissions/14622f20-5781-44cd-9f95-cad322cee63b

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
theorem _root_.solution (ρ : P →* ℂˣ) {x : Matrix (Fin r ⊕ Fin t) (Fin r) F}
    (hx : x ∉ suppSet t O ϖ P) : phiU O ϖ P ρ x = 0 := by
  unfold phiU
  rw [dif_neg]
  rintro ⟨⟨k, ek⟩, h2⟩
  exact hx ⟨⟨k, k.2, ek⟩, h2⟩
end GlobalTheory.SingleBlock
