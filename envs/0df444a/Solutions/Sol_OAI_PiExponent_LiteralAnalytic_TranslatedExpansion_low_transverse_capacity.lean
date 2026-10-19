-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.low_transverse_capacity
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T20:22:23.009825+00:00
-- url     : https://prove2.me/submissions/83be0aa8-2513-4396-9772-f4413f1e9e08

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights
import Theorems.Thm_OAI_PiExponent_Polynomials_realWeightedSimplex_map_filter_card_le

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem solution {nu : ℝ} (d : FixedData nu) (H : ℝ) :
    (((Finset.univ : Finset (indices d H)).filter
      (fun a => translatedIndexWeight d a ≤ (d.base.A : ℝ) * H)).card : ℝ) ≤
        (lowIndexCount d H : ℝ) := by
  change
    (((Finset.univ : Finset ((OAI.PiExponent.realWeightedSimplex
      (MatrixArithmetic.logWeights (finiteDenominators d)) H).map
        Finsupp.equivFunOnFinite.symm.toEmbedding)).filter
      (fun a => ∑ i : Fin d.m,
        MatrixArithmetic.logWeights (finiteDenominators d) i * (a.1 i : ℝ) ≤
          (d.base.A : ℝ) * H)).card : ℝ) ≤
      (OAI.PiExponent.realWeightedSimplex
        (MatrixArithmetic.logWeights (finiteDenominators d))
        ((d.base.A : ℝ) * H)).card
  exact OAI.PiExponent.Polynomials.realWeightedSimplex_map_filter_card_le
    (MatrixArithmetic.logWeights (finiteDenominators d)) H ((d.base.A : ℝ) * H)
    (by
      intro i
      have hx : d.x (i.val + 1) = MatrixArithmetic.logWeights (finiteDenominators d) i := by
        rw [d.x_log]
        rfl
      rw [← hx]
      linarith [d.x_one_le (i.val + 1)])