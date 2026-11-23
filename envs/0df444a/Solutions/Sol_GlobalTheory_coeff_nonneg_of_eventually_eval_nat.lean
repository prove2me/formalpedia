-- Prove2me | solution 1 for GlobalTheory.coeff_nonneg_of_eventually_eval_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:10:33.42189+00:00
-- url     : https://prove2.me/submissions/a919d38d-ba49-4585-909c-8fa5faf10839

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
theorem _root_.solution {P : ℚ[X]} {e : ℕ} (he : P.degree ≤ e)
    (h : ∀ᶠ n : ℕ in atTop, 0 ≤ P.eval (n : ℚ)) : 0 ≤ P.coeff e := by
  rcases he.eq_or_lt with he | he
  · rw [← natDegree_eq_of_degree_eq_some he]
    exact leadingCoeff_nonneg_of_eventually_eval_nat h
  · rw [coeff_eq_zero_of_degree_lt he]
end GlobalTheory
