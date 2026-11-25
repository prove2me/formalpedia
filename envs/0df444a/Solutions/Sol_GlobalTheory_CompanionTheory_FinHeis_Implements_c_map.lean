-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Implements.c_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:38:31.509987+00:00
-- url     : https://prove2.me/submissions/4fa078e7-01f5-49ca-8722-54cef03e27e2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Sys_rho_bijective
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Implements_injective

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
variable {S}
namespace GlobalTheory.CompanionTheory.FinHeis
namespace Implements
theorem _root_.solution [Nontrivial M] {g : X ≃+ X} {T : M →ₗ[ℂ] M} (h : Implements S g T) (x y : X) :
    S.c (g x) (g y) = S.c x y := by
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  have e : T (S.rho x (S.rho y v)) = T (S.c x y • S.rho (x + y) v) := by rw [S.rho_rho]
  rw [h.1, h.1, S.rho_rho, map_smul, h.1, map_add] at e
  have hne : S.rho (g x + g y) (T v) ≠ 0 := by
    intro h0
    apply hv
    apply h.injective
    apply (S.rho_bijective (g x + g y)).1
    rw [h0]; simp
  exact smul_left_injective ℂ hne e
end Implements
end GlobalTheory.CompanionTheory.FinHeis
