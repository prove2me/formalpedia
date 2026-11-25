-- Prove2me | solution 1 for GlobalTheory.PadicComplexHost.tendsto_inv_p_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:02:18.953581+00:00
-- url     : https://prove2.me/submissions/42f6cff3-21a2-4a5e-b779-43e8d39027d9

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Theorems.Thm_GlobalTheory_PadicComplexHost_inv_p_lt_one

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
theorem _root_.solution :
    Filter.Tendsto (fun n : ℕ => (p : ℝ)⁻¹ ^ n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_p_lt_one p)
end GlobalTheory.PadicComplexHost
