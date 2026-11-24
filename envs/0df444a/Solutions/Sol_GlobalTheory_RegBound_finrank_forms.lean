-- Prove2me | solution 1 for GlobalTheory.RegBound.finrank_forms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:55:15.796263+00:00
-- url     : https://prove2.me/submissions/cdf06783-9e47-4db8-88a2-f593376b35b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
namespace GlobalTheory.RegBound
theorem _root_.solution (e : ℕ) : finrank K (homogeneousSubmodule σ K e) = nmon σ e := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  exact finrank_eq_nat_card_basis (basisRestrictSupport K _)
end GlobalTheory.RegBound
