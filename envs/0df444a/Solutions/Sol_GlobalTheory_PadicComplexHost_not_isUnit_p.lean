-- Prove2me | solution 1 for GlobalTheory.PadicComplexHost.not_isUnit_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:28:03.437583+00:00
-- url     : https://prove2.me/submissions/5c7701a0-cbf5-4ea9-8aaa-28ddb51b6276

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Theorems.Thm_GlobalTheory_PadicComplexHost_valuation_coe_eq_norm
import Theorems.Thm_GlobalTheory_PadicComplexHost_norm_p
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
theorem _root_.solution : ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p]) := by
  intro h
  have h1 := (PadicComplexInt.integers p).one_of_isUnit h
  rw [map_natCast] at h1
  have h2 := valuation_coe_eq_norm p ((p : ℕ) : ℂ_[p])
  rw [h1, norm_p] at h2
  have := inv_p_lt_one p
  rw [← h2] at this
  simp at this
end GlobalTheory.PadicComplexHost
