-- Prove2me | solution 1 for GlobalTheory.rcout_coeff_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:31:25.354567+00:00
-- url     : https://prove2.me/submissions/4c80de71-5756-4d47-aca5-f345046306c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NewtonPolygonDominantIndexXSubCMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [NormedField K] (g : K[X]) (a : K) (k : ℕ) :
    ((X - C a) * g).coeff (k + 1) = g.coeff k - a * g.coeff (k + 1) := by
  rw [mul_comm, coeff_mul_X_sub_C]; ring
end GlobalTheory
