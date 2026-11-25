-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.shiftEnd_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:57:55.840604+00:00
-- url     : https://prove2.me/submissions/88a99485-158a-4ac9-96d1-b67a13e8b9f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
namespace GlobalTheory.WeilDeligne
theorem _root_.solution {n : ℕ} (v : Fin n → ℂ) (i : Fin n) :
    shiftEnd n v i = if 1 ≤ (i : ℕ) then v ⟨i - 1, by omega⟩ else 0 := rfl
end GlobalTheory.WeilDeligne
