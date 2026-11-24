-- Prove2me | solution 1 for GlobalTheory.roots_taylor_eq_map_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:32:50.589753+00:00
-- url     : https://prove2.me/submissions/fec6a019-00e8-4cf0-b1f2-bed5b2b2379e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardRootsClosedBallBoundsUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditivePolyTaylorCoeffSubNormLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FewRootsSmallDisc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Classical
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type*} [Field K] (p : K[X]) (w : K) :
    (taylor w p).roots = p.roots.map (fun x => x - w) := by
  have h := roots_comp_C_mul_X_add_C p (1 : K) w isUnit_one
  rw [taylor_apply]
  simpa using h
end GlobalTheory
