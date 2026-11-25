-- Prove2me | solution 1 for GroundTheory.PAdicHodge.mk_seriesEval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:19:05.466955+00:00
-- url     : https://prove2.me/submissions/7000c1fb-0e15-4cf6-9421-5d5a54f19772

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
namespace GroundTheory.PAdicHodge
theorem _root_.solution {z : B} (hz : z ∈ I) (f : ℚ⟦X⟧) (n : ℕ) :
    Ideal.Quotient.mk (I ^ n) (seriesEval I z hz f) =
      Ideal.Quotient.mk (I ^ n) (∑ i ∈ Finset.range n, algebraMap ℚ B (coeff i f) * z ^ i) := by
  have h := IsAdicComplete.mk_liftAlgHom I
    (fun n => truncEval (Ideal.Quotient.mk (I ^ n) z) (pow_mk_eq_zero I hz n))
    (fun hle => factorₐ_comp_truncEval I hz hle) n f
  rw [seriesEval, h, truncEval_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
end GroundTheory.PAdicHodge
