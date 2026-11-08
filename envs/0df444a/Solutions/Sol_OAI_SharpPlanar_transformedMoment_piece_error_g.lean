-- Prove2me | solution 1 for OAI.SharpPlanar.transformedMoment_piece_error_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:29:28.297619+00:00
-- url     : https://prove2.me/submissions/b8eda06f-767a-48b4-b4d5-0716c7a0d2e6

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_piece_rule_error_scaling_g
import Theorems.Thm_OAI_SharpPlanar_transformedMoment_piece_average_error_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Quadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Real Polynomial Finset MeasureTheory
open Polynomial.Chebyshev



open MeasureTheory Set
open scoped BigOperators

namespace SharpPlanar
open MeasureTheory

lemma transformedMoment_piece_error_g_oai (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {j : ℕ} (hj : j < 6) {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100)
    (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖pieceIntegral (fun t => finiteDensity c d j t*complexTransformedFactor m y ell t) j-
      pieceRule (fun t => finiteDensity c d j t*complexTransformedFactor m y ell t) j‖ <
        (1/10^22)/6 :=
  piece_rule_error_scaling_g _ _ (transformedMoment_piece_average_error_g c d hw hj hm0 hm1 hy ell)

end SharpPlanar


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.transformedMoment_piece_error_g_oai := @OAI.SharpPlanar.transformedMoment_piece_error_g_oai
