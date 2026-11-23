-- Prove2me | solution 1 for GlobalTheory.degree_le_of_eventually_eval_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:20.713859+00:00
-- url     : https://prove2.me/submissions/2eb19296-5f4f-48a7-9bb5-c88c45fafc0f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Theorems.Thm_GlobalTheory_leadingCoeff_nonneg_of_eventually_eval_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module
open GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory
theorem _root_.solution {P Q : ℚ[X]}
    (hP : ∀ᶠ n : ℕ in atTop, 0 ≤ P.eval (n : ℚ))
    (h : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) : P.degree ≤ Q.degree := by
  by_contra hlt
  push Not at hlt
  have hP0 : P ≠ 0 := by rintro rfl; simp at hlt
  have h1 : 0 ≤ (Q - P).leadingCoeff := leadingCoeff_nonneg_of_eventually_eval_nat (by
    filter_upwards [h] with n hn
    rw [eval_sub]; linarith)
  rw [leadingCoeff_sub_of_degree_lt' hlt] at h1
  have h2 := leadingCoeff_nonneg_of_eventually_eval_nat hP
  exact hP0 (leadingCoeff_eq_zero.1 (by linarith))
end GlobalTheory
