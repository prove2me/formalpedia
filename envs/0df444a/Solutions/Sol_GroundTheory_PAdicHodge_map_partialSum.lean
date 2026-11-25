-- Prove2me | solution 1 for GroundTheory.PAdicHodge.map_partialSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:18:18.338075+00:00
-- url     : https://prove2.me/submissions/d425b422-be3b-419a-9844-35557c43138a

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open PowerSeries
variable {B : Type*} [CommRing B] (I : Ideal B)
variable [Algebra ℚ B]
variable [IsAdicComplete I B]
variable {I}
omit [IsAdicComplete I B]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {B' : Type*} [CommRing B'] [Algebra ℚ B'] (F : B →+* B') (z : B)
    (f : ℚ⟦X⟧) (n : ℕ) :
    F (∑ i ∈ Finset.range n, algebraMap ℚ B (coeff i f) * z ^ i) =
      ∑ i ∈ Finset.range n, algebraMap ℚ B' (coeff i f) * F z ^ i := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, RingHom.map_rat_algebraMap]
end GroundTheory.PAdicHodge
