-- Prove2me | solution 1 for OAI.SharpPlanar.six_piece_error_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:12:47.317571+00:00
-- url     : https://prove2.me/submissions/866a945b-9bb8-499f-be8f-693a102efcef

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



open MeasureTheory Set
open scoped BigOperators

namespace SharpPlanar
open MeasureTheory

lemma six_piece_error_e_oai {F G : Fin 6 → ℂ} {ε : ℝ}
    (he : ∀ j, ‖F j-G j‖ < ε/6) : ‖(∑ j, F j)-(∑ j, G j)‖ < ε := by
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans_lt ?_
  have hs : ∑ j : Fin 6, ‖F j-G j‖ < ∑ j : Fin 6, ε/6 :=
    Finset.sum_lt_sum (by intro j _; exact (he j).le)
      ⟨0,Finset.mem_univ _,he 0⟩
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  linarith

end SharpPlanar


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.six_piece_error_e_oai := @OAI.SharpPlanar.six_piece_error_e_oai
