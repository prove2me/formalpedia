-- Prove2me | solution 1 for GlobalTheory.LengthDualFunctional.exists_dual_ne_zero_comp_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:40:04.706859+00:00
-- url     : https://prove2.me/submissions/9a969c8a-b120-4329-a421-d0ca89f2d041

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsDualNeZeroCompEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.LengthDualFunctional
open Module
namespace GlobalTheory.LengthDualFunctional
theorem _root_.solution {R : Type u_1} [CommRing R] [IsDomain R]
    {M : Type u_2} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    {f : M →ₗ[R] M} (h : LinearMap.det f = 0) :
    ∃ φ : Module.Dual R M, φ ≠ 0 ∧ φ ∘ₗ f = 0 := by
  have hd : LinearMap.det f.dualMap = 0 := by
    rw [LinearMap.det_dualMap]; exact h
  obtain ⟨φ, hφ, hφ0⟩ := (Submodule.ne_bot_iff _).mp (LinearMap.bot_lt_ker_of_det_eq_zero hd).ne'
  exact ⟨φ, hφ0, by simpa [LinearMap.dualMap_apply'] using hφ⟩
end GlobalTheory.LengthDualFunctional
