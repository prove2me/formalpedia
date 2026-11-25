-- Prove2me | solution 1 for GlobalTheory.T.iInf_sup_pow_eq_of_adic_compatible_ideals
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:20:45.895207+00:00
-- url     : https://prove2.me/submissions/d01140e1-7792-4fc7-bedd-136f1e0d3994

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IInfSupPowEqOfAdicCompatibleIdeals
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IInfSupPowEqOfAdicCompatibleIdealsStatement
import Theorems.Thm_GlobalTheory_iInf_sup_pow_eq_of_compatible


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (C : Type) [CommRing C] (J : Ideal C), IsAdicComplete J C → ∀ u : ℕ → Ideal C, (∀ e, u e = u (e + 1) ⊔ J ^ (e + 1)) → ∀ e, (⨅ l, u l) ⊔ J ^ (e + 1) = u e := by
  first | exact @GlobalTheory.iInf_sup_pow_eq_of_compatible | exact GlobalTheory.iInf_sup_pow_eq_of_compatible | (intros; apply GlobalTheory.iInf_sup_pow_eq_of_compatible <;> assumption)
end _root_.GlobalTheory.T
