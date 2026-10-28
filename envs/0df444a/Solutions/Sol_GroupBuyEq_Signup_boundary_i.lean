-- Prove2me | solution 1 for GroupBuyEq.Signup.boundary_i
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:28:39.355827+00:00
-- url     : https://prove2.me/submissions/aa4df03e-58f2-464d-819e-88dc45b0f37b

import Mathlib
import Definitions.Def_GroupBuyEq_Signup_Model

open GroupBuyEq.Signup in
theorem solution (P : Params) (hP : P.Standing) (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure μ] (E : Profile) (hE : IsEquilibrium P μ E) :
    (∀ k : ℕ, k < P.M1 → E.pi1 k P.T = 0) ∧ (∀ k : ℕ, k < P.M2 → E.pi2 k P.T = 0) := by
  have hT : P.T ∈ Set.Icc 0 P.T := ⟨le_of_lt hP.1, le_refl _⟩
  obtain ⟨_, _, _, _, h2, h1⟩ := hE
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · rw [h1 k hk P.T hT, sub_self, intervalIntegral.integral_same]
  · rw [h2 k hk P.T hT, sub_self, intervalIntegral.integral_same]
