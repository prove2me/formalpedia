-- Prove2me | solution 1 for GlobalTheory.AppellHumbert.eq_sum_re_im
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:01:53.246277+00:00
-- url     : https://prove2.me/submissions/a0f5af76-4504-4a1e-80c3-ad3a78a88a3f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertNormalFormOfLinearExponent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.AppellHumbert
open Complex Matrix Filter Topology
open scoped BigOperators Real
namespace GlobalTheory.AppellHumbert
namespace _root_.GlobalTheory.AppellHumbert
theorem _root_.solution {g : ℕ} (u : Fin g → ℂ) :
    u = ∑ j, ((u j).re • (Pi.single j (1 : ℂ) : Fin g → ℂ)
      + (u j).im • (Pi.single j I : Fin g → ℂ)) := by
  ext i
  simp [Finset.sum_apply, Finset.sum_add_distrib, Pi.single_apply, Complex.re_add_im]
end _root_.GlobalTheory.AppellHumbert
end GlobalTheory.AppellHumbert
