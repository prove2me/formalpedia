-- Prove2me | solution 1 for GroundTheory.LocalField.root_pow_mem_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:15:25.766513+00:00
-- url     : https://prove2.me/submissions/9f632ba4-0b16-41c0-85a2-6e204e27ce6c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LubinTateReciprocity_RootEval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open PowerSeries
variable {B : Type*} [CommRing B] {I : Ideal B} {P : Polynomial B}
namespace GroundTheory.LocalField
theorem _root_.solution (hP : P.IsDistinguishedAt I) :
    AdjoinRoot.root P ^ P.natDegree ∈ I.map (AdjoinRoot.of P) := by
  have h : Polynomial.eval₂ (AdjoinRoot.of P) (AdjoinRoot.root P)
      (Polynomial.X ^ P.natDegree +
        ∑ i ∈ Finset.range P.natDegree, Polynomial.C (P.coeff i) * Polynomial.X ^ i) = 0 := by
    rw [← hP.monic.as_sum]
    exact AdjoinRoot.eval₂_root P
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at h
  rw [eq_neg_of_add_eq_zero_left h, neg_mem_iff]
  refine Ideal.sum_mem _ fun i hi => ?_
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
  exact Ideal.mul_mem_right _ _
    (Ideal.mem_map_of_mem _ (hP.mem (Finset.mem_range.mp hi)))
end GroundTheory.LocalField
