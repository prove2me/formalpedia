-- Prove2me | solution 1 for OAI.SharpPlanar.piece_rule_error_scaling_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:46:08.211564+00:00
-- url     : https://prove2.me/submissions/f2cdce4c-3573-44df-bfa6-7837c068773b

import Mathlib
import Definitions.Def_OAIQ098E018
import Theorems.Thm_OAI_SharpPlanar_pieceIntegral_affine_e

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

lemma piece_rule_error_scaling_e_oai (F : ℂ → ℂ) (j : ℕ) {ε : ℝ}
    (he : ‖(1/2:ℂ) * (∫ x in (-1:ℝ)..1, F (diskAffine j x)) -
      ∑ v : Fin 256, (fejerWeight v.val:ℂ)*
        F (diskAffine j (fejerNode v.val))‖ < ε) :
    ‖pieceIntegral F j-pieceRule F j‖ < ε/6 := by
  rw [pieceIntegral_affine_e,pieceRule]
  have hid (a b : ℂ) : (1/12:ℂ)*a-(1/6:ℂ)*b =
      (1/6:ℂ)*((1/2:ℂ)*a-b) := by ring
  rw [hid,norm_mul]
  norm_num only [norm_div,norm_one,Complex.norm_ofNat] at *
  linarith

end SharpPlanar


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.piece_rule_error_scaling_e_oai := @OAI.SharpPlanar.piece_rule_error_scaling_e_oai
