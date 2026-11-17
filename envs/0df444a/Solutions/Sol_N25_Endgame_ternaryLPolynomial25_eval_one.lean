-- Prove2me | solution 1 for N25.Endgame.ternaryLPolynomial25_eval_one
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:24:25.157063+00:00
-- url     : https://prove2.me/submissions/272dca5e-8085-4bbf-8535-3dd039757baa

import Definitions.Def_N25_GenusFourNumerator

/-! # Reconstruction from four counts and the genus-four functional equation

The hypotheses retain the degree bound, constant coefficient, Newton identities,
and functional equation explicitly. Geometric producers of these hypotheses are
separate from this integer-polynomial calculation.
-/

namespace N25

namespace Endgame

/-- The ternary numerator takes value seventy-one at one. -/
theorem _root_.solution : ternaryLPolynomial25.eval 1 = 71 := by
  norm_num [ternaryLPolynomial25]

end Endgame

end N25
