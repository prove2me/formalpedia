-- Prove2me | solution 1 for GlobalTheory.UnitarySwap.form_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:11:00.955078+00:00
-- url     : https://prove2.me/submissions/61bec348-afb0-45e5-af3f-9c4e7ae374e9

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Theorems.Thm_GlobalTheory_UnitarySwap_form_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnitarySwap
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable {n : ℕ} {σ : L →+* L}
omit [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.UnitarySwap
theorem _root_.solution (J : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    form σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have : σ ∘ (Pi.single i 1 : Fin n → L) = Pi.single i 1 := by
    funext k; by_cases h : k = i <;> simp [h]
  rw [form_apply, this]
  simp
end GlobalTheory.UnitarySwap
