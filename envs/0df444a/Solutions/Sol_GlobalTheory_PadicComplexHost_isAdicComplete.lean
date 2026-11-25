-- Prove2me | solution 1 for GlobalTheory.PadicComplexHost.isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:49:06.542841+00:00
-- url     : https://prove2.me/submissions/c9bd4bdd-f75b-44b5-b865-4a2961a0f91b

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Theorems.Thm_GlobalTheory_PadicComplexHost_isHausdorff
import Theorems.Thm_GlobalTheory_PadicComplexHost_isPrecomplete

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
theorem _root_.solution : IsAdicComplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] :=
  { isHausdorff p, isPrecomplete p with }
end GlobalTheory.PadicComplexHost
