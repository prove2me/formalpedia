-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Implements.comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:30.218091+00:00
-- url     : https://prove2.me/submissions/a0b781f3-f4ff-4205-a4d1-1ef32a7d6881

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
theorem _root_.solution {g g' : X ≃+ X} {T T' : M →ₗ[ℂ] M} (h : Implements S g T) (h' : Implements S g' T') :
    Implements S (g'.trans g) (T ∘ₗ T') :=
  ⟨fun x v => by simp [h'.1, h.1], fun u v => by simp [h.2, h'.2]⟩
end Implements
end GlobalTheory.CompanionTheory.FinHeis
