-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.isNilpotent_shiftEnd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:18:18.826395+00:00
-- url     : https://prove2.me/submissions/32f35b13-824a-4a5a-b501-77b863c3c169

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
import Theorems.Thm_GlobalTheory_WeilDeligne_shiftEnd_pow_apply

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
theorem _root_.solution (n : ℕ) : IsNilpotent (shiftEnd n) :=
  ⟨n, LinearMap.ext fun v => funext fun i => by
    rw [shiftEnd_pow_apply, if_neg (by omega)]; rfl⟩
end GlobalTheory.WeilDeligne
