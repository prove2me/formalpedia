-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Inh.cyclic_vac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:38:39.966712+00:00
-- url     : https://prove2.me/submissions/b0e5c4d3-baae-4510-b466-8ccfb3082159

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
variable {S}
open GlobalTheory.CompanionTheory.FinHeis.Inh
namespace GlobalTheory.CompanionTheory.FinHeis.Inh
theorem _root_.solution : Cyclic sysEx vac := by
  unfold Cyclic
  rw [eq_top_iff]
  intro f _
  have r0 : red 0 = 0 := by decide
  have r1 : red 1 = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have : f = f 0 • sysEx.rho (0, 0) vac + f 1 • sysEx.rho (1, 0) vac := by
    ext t
    rcases zmod2 t with rfl | rfl <;> simp [sysEx, rhoEx, vac, r0, r1, h11, e_zero]
  rw [this]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
end GlobalTheory.CompanionTheory.FinHeis.Inh
