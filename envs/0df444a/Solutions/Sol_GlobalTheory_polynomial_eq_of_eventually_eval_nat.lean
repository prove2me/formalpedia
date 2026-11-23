-- Prove2me | solution 1 for GlobalTheory.polynomial_eq_of_eventually_eval_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:28.351831+00:00
-- url     : https://prove2.me/submissions/4ab4fd11-a1a4-47a6-a397-af1e6b14baf0

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
theorem _root_.solution {P Q : ℚ[X]}
    (h : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = Q.eval (n : ℚ)) : P = Q := by
  apply eq_of_infinite_eval_eq
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  refine Set.Infinite.mono (s := (Nat.cast : ℕ → ℚ) '' Set.Ici N) ?_
    ((Set.Ici_infinite N).image Nat.cast_injective.injOn)
  rintro _ ⟨n, hn, rfl⟩
  exact hN n hn
end GlobalTheory
