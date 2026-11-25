-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.implements_iff_ip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:41:08.242163+00:00
-- url     : https://prove2.me/submissions/a91bbdd8-cba7-46f6-a7e0-eca9fd523ccb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinHeis
variable {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (S : Sys X M)
namespace GlobalTheory.CompanionTheory.FinHeis
theorem _root_.solution (g : X ≃+ X) (T : M →ₗ[ℂ] M) :
    Implements S g T ↔ (∀ x v, T (S.rho x v) = S.rho (g x) (T v)) ∧ ∀ u v, ip S (T u) (T v) = ip S u v :=
  ⟨fun h => ⟨h.1, fun u v => h.2 v u⟩, fun h => ⟨h.1, fun u v => h.2 v u⟩⟩
end GlobalTheory.CompanionTheory.FinHeis
