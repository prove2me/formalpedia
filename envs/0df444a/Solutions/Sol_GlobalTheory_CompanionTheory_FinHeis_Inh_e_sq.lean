-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Inh.e_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:43.94784+00:00
-- url     : https://prove2.me/submissions/2cdcc72b-d2dd-496f-a434-3300f5b19c9f

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
theorem _root_.solution (n : ZMod 4) : e n ^ 2 = 1 ↔ 2 * n = 0 := by
  rw [sq, ← e_add, ← two_mul]
  have : 2 * n = 0 ∨ 2 * n = 2 := by revert n; decide
  rcases this with h | h
  · rw [h, e_zero]; simp
  · rw [h, e_two]
    constructor
    · intro hh; norm_num at hh
    · intro hh; exact absurd hh (by decide)
end GlobalTheory.CompanionTheory.FinHeis.Inh
