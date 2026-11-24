-- Prove2me | solution 1 for GlobalTheory.IsHilbertPoly.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:35:07.281585+00:00
-- url     : https://prove2.me/submissions/e5e97de9-5db5-4f85-9145-436623636a30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Theorems.Thm_GlobalTheory_polynomial_eq_of_eventually_eval_int

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
open DirectSum Module GradedHilbert
variable {k : Type*} [Field k] {M' M M'' : Type*} [AddCommGroup M'] [Module k M']
  [AddCommGroup M] [Module k M] [AddCommGroup M''] [Module k M'']
namespace GlobalTheory
namespace IsHilbertPoly
theorem _root_.solution {ℳ : ℤ → Submodule k M} {P Q : ℚ[X]} (hP : IsHilbertPoly ℳ P)
    (hQ : IsHilbertPoly ℳ Q) : P = Q := by
  apply polynomial_eq_of_eventually_eval_int
  filter_upwards [hP.eventually_eq, hQ.eventually_eq] with n h1 h2
  rw [← h1, ← h2]
end IsHilbertPoly
end GlobalTheory
