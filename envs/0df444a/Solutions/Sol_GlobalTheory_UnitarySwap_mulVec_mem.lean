-- Prove2me | solution 1 for GlobalTheory.UnitarySwap.mulVec_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:48:27.022631+00:00
-- url     : https://prove2.me/submissions/9dd93288-b503-4159-bde7-1c56517e3b7f

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnitarySwap
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable {n : ℕ} {σ : L →+* L}
namespace GlobalTheory.UnitarySwap
theorem _root_.solution {M : Matrix (Fin n) (Fin n) L} (hM : ∀ i j, M i j ∈ intL L) {v : Fin n → L}
    (hv : v ∈ intVec L n) : M *ᵥ v ∈ intVec L n := fun i => by
  show ∑ j, M i j * v j ∈ intL L
  exact Subring.sum_mem _ fun j _ => mul_mem (hM i j) (hv j)
end GlobalTheory.UnitarySwap
