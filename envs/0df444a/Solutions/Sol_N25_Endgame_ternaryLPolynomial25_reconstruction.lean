-- Prove2me | solution 1 for N25.Endgame.ternaryLPolynomial25_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:05.529608+00:00
-- url     : https://prove2.me/submissions/81b757f9-bfd3-459c-89de-f4bd50ee00ff

import Definitions.Def_N25_GenusFourNumerator
import Theorems.Thm_N25_genusFour_numerator_reconstruction

/-! # Reconstruction from four counts and the genus-four functional equation

The hypotheses retain the degree bound, constant coefficient, Newton identities,
and functional equation explicitly. Geometric producers of these hypotheses are
separate from this integer-polynomial calculation.
-/

namespace N25

namespace Endgame

/-- Reconstruction at three uses a different reciprocal polynomial. -/
theorem _root_.solution (L : Polynomial ℤ)
    (hdegree : L.natDegree ≤ 8) (hzero : L.coeff 0 = 1)
    (hnewton : CountNewtonFourEquations 3 5 5 20 89
      (L.coeff 1) (L.coeff 2) (L.coeff 3) (L.coeff 4))
    (hrec : ∀ i ≤ 8, L.coeff (8 - i) * 3 ^ i = 3 ^ 4 * L.coeff i) :
    L = ternaryLPolynomial25 := by
  have hc : CountNewtonFourEquations 3 5 5 20 89 1 (-2) (-5) 1 := by
    norm_num [CountNewtonFourEquations, NewtonFourEquations]
  rw [genusFour_numerator_reconstruction L 3 1 (-2) (-5) 1 5 5 20 89
    (by norm_num) hdegree hzero hnewton hc hrec]
  norm_num [genusFourNumerator, ternaryLPolynomial25]
  ring

end Endgame

end N25
