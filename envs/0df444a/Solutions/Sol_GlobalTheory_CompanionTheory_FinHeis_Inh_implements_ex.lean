-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Inh.implements_ex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:38:45.203323+00:00
-- url     : https://prove2.me/submissions/a0e74bc8-9d1c-4998-a17c-89d418bb4c6e

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
theorem _root_.solution : Implements sysEx shear TEx := by
  refine ⟨fun x v => ?_, fun u v => ?_⟩
  · ext t
    obtain ⟨a, b⟩ := x
    show e (ph t) * (e (a * b + b * dbl t) * v (t + red a))
      = e (a * (b + a) + (b + a) * dbl t) * (e (ph (t + red a)) * v (t + red a))
    rw [← mul_assoc, ← mul_assoc, ← e_add, ← e_add]
    congr 2
    revert a b t; decide
  · show BEx _ _ = BEx _ _
    simp only [BEx_apply, TEx, LinearMap.coe_mk, AddHom.coe_mk, map_mul]
    linear_combination ((starRingEnd ℂ) (u 0) * v 0) * e_conj (ph 0) + ((starRingEnd ℂ) (u 1) * v 1) * e_conj (ph 1)
end GlobalTheory.CompanionTheory.FinHeis.Inh
