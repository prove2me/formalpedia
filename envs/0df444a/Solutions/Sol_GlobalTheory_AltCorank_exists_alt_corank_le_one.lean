-- Prove2me | solution 1 for GlobalTheory.AltCorank.exists_alt_corank_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:28:48.426634+00:00
-- url     : https://prove2.me/submissions/7296ab0d-1719-4a8c-b297-99d525c0f2a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAlternatingFormLeftCorankLeOne
import Theorems.Thm_GlobalTheory_AltCorank_good_of_finrank_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AltCorank
open Module
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.AltCorank
theorem _root_.solution :
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
      (S₁ S₂ : Submodule K V), Module.finrank K S₁ = Module.finrank K S₂ →
      ∃ ω : V →ₗ[K] V →ₗ[K] K, (∀ v, ω v v = 0) ∧ ∀ x : Fin 2 → V, (∀ a, x a ∈ S₁) →
        (∀ a, ∀ y ∈ S₂, ω (x a) y = 0) → ¬ LinearIndependent K x :=
  fun _ _ _ _ _ _ S₁ S₂ h => good_of_finrank_eq _ S₁ S₂ h rfl
end GlobalTheory.AltCorank
