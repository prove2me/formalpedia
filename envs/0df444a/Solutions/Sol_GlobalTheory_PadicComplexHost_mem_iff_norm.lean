-- Prove2me | solution 1 for GlobalTheory.PadicComplexHost.mem_iff_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:01:43.200012+00:00
-- url     : https://prove2.me/submissions/27391b74-829b-42bb-86e4-515c704e85b9

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Theorems.Thm_GlobalTheory_PadicComplexHost_valuation_coe_eq_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Ideal
open GlobalTheory GlobalTheory.PadicComplexHost
variable (p : ℕ) [hp : Fact p.Prime]
namespace GlobalTheory.PadicComplexHost
theorem _root_.solution (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  rw [← valuation_coe_eq_norm]
  change Valued.v x ≤ 1 ↔ _
  exact_mod_cast Iff.rfl
end GlobalTheory.PadicComplexHost
