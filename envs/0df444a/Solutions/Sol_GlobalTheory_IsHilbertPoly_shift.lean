-- Prove2me | solution 1 for GlobalTheory.IsHilbertPoly.shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:53:53.620009+00:00
-- url     : https://prove2.me/submissions/cae99181-2e59-40e0-a681-03a89e9a14c1

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
open DirectSum Module GradedHilbert
variable {k : Type*} [Field k] {M' M M'' : Type*} [AddCommGroup M'] [Module k M']
  [AddCommGroup M] [Module k M] [AddCommGroup M''] [Module k M'']
namespace GlobalTheory
namespace IsHilbertPoly
theorem _root_.solution {ℳ : ℤ → Submodule k M} {P : ℚ[X]} (hP : IsHilbertPoly ℳ P)
    (d : ℤ) : IsHilbertPoly (fun n => ℳ (n + d)) (P.comp (X + C (d : ℚ))) where
  finite n := hP.finite (n + d)
  eventually_eq := by
    filter_upwards [(Filter.tendsto_atTop_add_const_right atTop d Filter.tendsto_id).eventually
      hP.eventually_eq] with n hn
    simp only [id_eq] at hn
    rw [hn, eval_comp]
    simp
end IsHilbertPoly
end GlobalTheory
