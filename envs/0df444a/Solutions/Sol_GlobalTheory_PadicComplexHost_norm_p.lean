-- Prove2me | solution 1 for GlobalTheory.PadicComplexHost.norm_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:08:57.381914+00:00
-- url     : https://prove2.me/submissions/2cae940d-a5db-4bc6-809d-55fd9f19b581

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
theorem _root_.solution : ‖((p : ℕ) : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [← valuation_coe_eq_norm, PadicComplex.valuation_p]; simp
end GlobalTheory.PadicComplexHost
