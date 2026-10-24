-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_support_subset_simplex
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:41:57.214082+00:00
-- url     : https://prove2.me/submissions/0dabf4ea-1662-47cb-8266-69c02324a113

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_support_subset_simplex_of_positive_weights
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (P : WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H) :
    P.1.support.map Finsupp.equivFunOnFinite.toEmbedding ⊆
      realWeightedSimplex
        (InterpolationMatrix.columnWeights d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d))) H := by
  apply weighted_support_subset_simplex_of_positive_weights
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [InterpolationMatrix.columnWeights] using d.w0_pos
  · have hq : 2 ≤ finiteDenominators d j := d.approximations j.1 |>.1
    have hlog : 0 < Real.log (finiteDenominators d j) := by
      apply Real.log_pos
      exact_mod_cast (by omega : 1 < finiteDenominators d j)
    change 0 < (Nat.ceil (Real.log (finiteDenominators d j)) : Real)
    exact_mod_cast (Nat.ceil_pos.mpr hlog)
