-- Prove2me | solution 1 for GlobalTheory.InertZeta.smul_mem_integral_submodule_of_valuation_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:47:54.571251+00:00
-- url     : https://prove2.me/submissions/7aa54f48-9cf7-468c-a380-5cb3a3b0f4f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LatticeAddVectorDetValuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.InertZeta
namespace GlobalTheory.InertZeta
theorem _root_.solution {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
    {P : Submodule (Formalism.UG.intL L) (Fin n → L)} {x : L} (hx : Valued.v x ≤ 1) {w : Fin n → L} (hw : w ∈ P) :
    x • w ∈ P :=
  P.smul_mem (⟨x, hx⟩ : Formalism.UG.intL L) hw
end GlobalTheory.InertZeta
