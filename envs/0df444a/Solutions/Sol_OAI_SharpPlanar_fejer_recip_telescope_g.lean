-- Prove2me | solution 1 for OAI.SharpPlanar.fejer_recip_telescope_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:06:11.73785+00:00
-- url     : https://prove2.me/submissions/1c009908-7315-40f1-b3a8-eba54e5e41dd

import Mathlib

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Quadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Real Polynomial Finset MeasureTheory
open Polynomial.Chebyshev

namespace SharpPlanar

lemma fejer_recip_telescope_g_oai (a : ℕ) (ha : 1 ≤ a) :
    (2:ℝ)/(4*(a:ℝ)^2-1) = 1/(2*(a:ℝ)-1)-1/(2*(a:ℝ)+1) := by
  have ha' : (1:ℝ) ≤ a := by exact_mod_cast ha
  have h₁ : 2*(a:ℝ)-1 ≠ 0 := by linarith
  have h₂ : 2*(a:ℝ)+1 ≠ 0 := by linarith
  have h₃ : 4*(a:ℝ)^2-1 ≠ 0 := by nlinarith
  field_simp
  ring

end SharpPlanar



open MeasureTheory Set
open scoped BigOperators


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.fejer_recip_telescope_g_oai := @OAI.SharpPlanar.fejer_recip_telescope_g_oai
