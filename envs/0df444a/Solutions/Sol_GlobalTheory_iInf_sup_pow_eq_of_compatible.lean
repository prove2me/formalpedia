-- Prove2me | solution 1 for GlobalTheory.iInf_sup_pow_eq_of_compatible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:00:06.715977+00:00
-- url     : https://prove2.me/submissions/b9ffc997-f2ef-43b8-937f-e58d7fbb9992

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IInfSupPowEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IInfSupPowEqOfAdicCompatibleIdeals
import Theorems.Thm_GlobalTheory_InfimumSupPowerIdeal_iInf_sup_pow_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (C : Type) [CommRing C] (J : Ideal C), IsAdicComplete J C → ∀ u : ℕ → Ideal C,
      (∀ e, u e = u (e + 1) ⊔ J ^ (e + 1)) → ∀ e, (⨅ l, u l) ⊔ J ^ (e + 1) = u e := by
  first
  | exact @_root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq
  | exact _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq
  | (apply _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq ..)
end GlobalTheory
