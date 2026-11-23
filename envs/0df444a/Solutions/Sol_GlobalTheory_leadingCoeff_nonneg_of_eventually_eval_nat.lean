-- Prove2me | solution 1 for GlobalTheory.leadingCoeff_nonneg_of_eventually_eval_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:27.588822+00:00
-- url     : https://prove2.me/submissions/cc005af0-4734-4594-a254-ab816826688a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat

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
theorem _root_.solution {P : ℚ[X]}
    (h : ∀ᶠ n : ℕ in atTop, 0 ≤ P.eval (n : ℚ)) : 0 ≤ P.leadingCoeff := by
  by_contra hneg
  push Not at hneg
  rcases le_or_gt P.degree 0 with h0 | h0
  · obtain ⟨n, hn⟩ := h.exists
    rw [eq_C_of_degree_le_zero h0] at hn hneg
    simp only [eval_C, leadingCoeff_C] at hn hneg
    exact absurd hn (not_le.2 hneg)
  · have := ((tendsto_atBot_of_leadingCoeff_nonpos P h0 hneg.le).comp
      (tendsto_natCast_atTop_atTop (R := ℚ))).eventually (eventually_lt_atBot 0)
    obtain ⟨n, h1, h2⟩ := (h.and this).exists
    exact absurd h1 (not_le.2 h2)
end GlobalTheory
