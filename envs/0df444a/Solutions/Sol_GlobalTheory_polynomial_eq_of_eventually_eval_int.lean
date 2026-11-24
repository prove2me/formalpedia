-- Prove2me | solution 1 for GlobalTheory.polynomial_eq_of_eventually_eval_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:29:06.945133+00:00
-- url     : https://prove2.me/submissions/0147db68-f21c-44b4-b2fe-212d60f95940

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter
open GlobalTheory
variable {K : Type*} [Field K]
variable [CharZero K]
namespace GlobalTheory
theorem _root_.solution {P Q : K[X]}
    (h : ∀ᶠ n : ℤ in atTop, P.eval (n : K) = Q.eval (n : K)) : P = Q := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
  apply eq_of_infinite_eval_eq
  have hinf : ((fun n : ℤ => (n : K)) '' Set.Ici N).Infinite :=
    Set.Infinite.image Int.cast_injective.injOn (Set.Ici_infinite N)
  refine Set.Infinite.mono ?_ hinf
  rintro _ ⟨n, hn, rfl⟩
  exact hN n hn
end GlobalTheory
