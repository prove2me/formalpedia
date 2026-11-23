-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Implements.injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:43.074874+00:00
-- url     : https://prove2.me/submissions/237b3e11-7bba-49ce-97fe-5cf81faa61bb

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
namespace GlobalTheory.CompanionTheory.FinHeis
namespace Implements
theorem _root_.solution {g : X ≃+ X} {T : M →ₗ[ℂ] M} (h : Implements S g T) : Function.Injective T := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  by_contra hne
  have := S.B_pos v hne
  rw [← h.2, hv] at this
  simp at this
end Implements
end GlobalTheory.CompanionTheory.FinHeis
