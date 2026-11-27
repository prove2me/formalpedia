-- Prove2me | solution 1 for GlobalTheory.min_le_heightOneOrd_vw_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:44:45.854576+00:00
-- url     : https://prove2.me/submissions/371851da-c349-4056-9c8f-33250dd1acb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
open GlobalTheory
variable {A : Type*} [CommRing A] [IsDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
variable {K}
variable [IsNoetherianRing A]
variable [IsIntegrallyClosed A]
variable (p : Ideal A) [p.IsPrime] (hp : p.height = 1)
namespace GlobalTheory
theorem _root_.solution {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (heightOneOrd_vw p hp x) (heightOneOrd_vw p hp y) ≤ heightOneOrd_vw p hp (x + y) := by
  have := isDiscreteValuationRing_of_height_eq_one p hp (primeLocalSubalgebra K p)
  have h := Ring.ordFrac_add (R := primeLocalSubalgebra K p) x y hxy
  rw [ordFrac_eq_heightOneOrdHom p hp, heightOneOrdHom_eq_exp p hp hx,
    heightOneOrdHom_eq_exp p hp hy, heightOneOrdHom_eq_exp p hp hxy, min_le_iff,
    WithZero.exp_le_exp, WithZero.exp_le_exp] at h
  exact min_le_iff.mpr h
end GlobalTheory
