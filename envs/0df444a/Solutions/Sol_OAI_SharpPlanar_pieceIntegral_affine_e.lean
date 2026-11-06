-- Prove2me | solution 1 for OAI.SharpPlanar.pieceIntegral_affine_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:45:45.999737+00:00
-- url     : https://prove2.me/submissions/c88e86eb-4344-4925-8d74-333b26b528aa

import Mathlib
import Definitions.Def_OAIQ098E018

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

lemma pieceIntegral_affine_e_oai (F : ℂ → ℂ) (j : ℕ) :
    pieceIntegral F j = (1/12:ℂ) * ∫ x in (-1:ℝ)..1,
      F (diskAffine j x) := by
  have he := intervalIntegral.smul_integral_comp_add_mul (fun x : ℝ => F x)
    (a := -1) (b := 1) (1/12) (diskCenter j)
  have ha : diskCenter j + (1/12:ℝ)*(-1) = (j:ℝ)/6 := by
    unfold diskCenter; ring
  have hb : diskCenter j + (1/12:ℝ)*1 = ((j:ℝ)+1)/6 := by
    unfold diskCenter; ring
  rw [ha,hb] at he
  have hint : (fun x : ℝ => F (diskAffine j x)) =
      (fun x : ℝ => F ((diskCenter j + (1/12:ℝ)*x : ℝ):ℂ)) := by
    funext x
    congr 1
    simp only [diskAffine,Complex.ofReal_add,Complex.ofReal_mul,
      Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
    ring
  rw [pieceIntegral,hint,← he]
  simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_one,
    Complex.ofReal_ofNat]

end SharpPlanar


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.pieceIntegral_affine_e_oai := @OAI.SharpPlanar.pieceIntegral_affine_e_oai
