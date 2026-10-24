-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.support_sum_reindex
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:35:24.502848+00:00
-- url     : https://prove2.me/submissions/b0c28c27-492c-42a1-9eac-4dcb3b3535b1

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem solution
    (m : Nat) (P : MvPolynomial (Fin m) Complex)
    (f : (Fin m →₀ Nat) → Complex) :
    (∑ a ∈ P.support, f a * P.coeff a) =
      ∑ a ∈ P.support.map Finsupp.equivFunOnFinite.toEmbedding,
        f (InterpolationMatrix.exponentVector a) *
          P.coeff (InterpolationMatrix.exponentVector a) := by
  classical
  simp [Finset.sum_map, InterpolationMatrix.exponentVector]