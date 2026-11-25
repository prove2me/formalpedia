-- Prove2me | solution 1 for GlobalTheory.PadicComplexHost.inv_p_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:43:20.235135+00:00
-- url     : https://prove2.me/submissions/7d19d79b-86aa-400b-95d1-105c3b849657

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm

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
theorem _root_.solution : (p : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
end GlobalTheory.PadicComplexHost
