-- Prove2me | solution 1 for GlobalTheory.rcout_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:31:26.563676+00:00
-- url     : https://prove2.me/submissions/9975a96d-d986-4293-b05a-e936e7b7a0a7

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
theorem _root_.solution {K : Type} [NormedField K] (g : K[X]) (a : K) :
    ((X - C a) * g).coeff 0 = -(a * g.coeff 0) := by
  rw [mul_coeff_zero]; simp
end GlobalTheory
