-- Prove2me | solution 1 for OAI.SharpPlanar.transformedMoment_rule_error_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:29:35.992647+00:00
-- url     : https://prove2.me/submissions/09d848eb-2893-4a4b-9f4a-92402113c7a0

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_six_piece_error_g
import Theorems.Thm_OAI_SharpPlanar_transformedMoment_piece_error_g

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

lemma transformedMoment_rule_error_g_oai (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100) (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖(∑ j : Fin 6, pieceIntegral
        (fun t => finiteDensity c d j t*complexTransformedFactor m y ell t) j)-
      ∑ j : Fin 6, pieceRule
        (fun t => finiteDensity c d j t*complexTransformedFactor m y ell t) j‖ < 1/10^22 :=
  six_piece_error_g (fun j => transformedMoment_piece_error_g c d hw j.isLt hm0 hm1 hy ell)

end SharpPlanar


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.transformedMoment_rule_error_g_oai := @OAI.SharpPlanar.transformedMoment_rule_error_g_oai
