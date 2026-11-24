-- Prove2me | solution 1 for GlobalTheory.prod_finset_fin_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:53.685688+00:00
-- url     : https://prove2.me/submissions/965a2def-5729-4326-a11e-8740b72ed568

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AutomorphyFactorExpLinearOfCube

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
namespace GlobalTheory
theorem _root_.solution {M : Type*} [CommMonoid M] (f : Finset (Fin 3) → M) :
    ∏ I, f I = f ∅ * (f {0} * (f {1} * (f {2} * (f {0, 1} * (f {0, 2} * (f {1, 2} *
      f {0, 1, 2})))))) := by
  have e : (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  rw [e]
  repeat rw [Finset.prod_insert (by decide)]
  rw [Finset.prod_singleton]
end GlobalTheory
