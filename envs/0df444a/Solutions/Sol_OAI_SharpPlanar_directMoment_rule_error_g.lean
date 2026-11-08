-- Prove2me | solution 1 for OAI.SharpPlanar.directMoment_rule_error_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:15:02.201841+00:00
-- url     : https://prove2.me/submissions/87542f74-c29a-459a-8a8e-0985919be4bf

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G1643
import Theorems.Thm_OAI_SharpPlanar_directMoment_piece_error_g
import Theorems.Thm_OAI_SharpPlanar_six_piece_error_g

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

lemma directMoment_rule_error_g_oai (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100) (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖(∑ j : Fin 6, pieceIntegral
        (fun t => finiteDensity c d j t*complexDirectFactor m y ell t) j)-
      ∑ j : Fin 6, pieceRule
        (fun t => finiteDensity c d j t*complexDirectFactor m y ell t) j‖ < 1/10^22 :=
  six_piece_error_g (fun j => directMoment_piece_error_g c d hw j.isLt hm0 hm1 hy ell)

end SharpPlanar


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.directMoment_rule_error_g_oai := @OAI.SharpPlanar.directMoment_rule_error_g_oai
