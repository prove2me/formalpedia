-- Prove2me | solution 1 for MagicSquares.symmetric_magic_three_classify
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-18T14:05:46.898467+00:00
-- url     : https://prove2.me/submissions/0c4a3f50-302e-4de2-af47-fe7f6a02249b

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresSpecial3

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

/-- Solution for `MagicSquares.symmetric_magic_three_classify`.

Write the array as `[[a,b,c],[d,m,f],[g,h,i]]`. Symmetry identifies `b = d`,
`c = g` and `f = h`, so the eight line identities collapse to five:
the three rows, the main diagonal `a + m + i = 3e`, and the anti-diagonal
`c + m + g = 2c + m = 3e`. The last one gives `c = e` immediately, and the rows
then determine `b`, `f`, `m` and `i` from `a`:

```
b = 2e - a,  m = e,  f = a,  g = e,  h = a,  i = 2e - a.
```

That is exactly `symmMagic3 e a` with `a = M 0 0`. The whole classification is a
single `omega` call on the five line equations plus the three symmetry
identities. -/
theorem solution (e : ℕ) (M : Square 3 ℕ)
    (hM : IsMagic M (3 * e)) (hsym : IsSymmetric M) :
    M = symmMagic3 e (M 0 0) := by
  have hR0 : M 0 0 + M 0 1 + M 0 2 = 3 * e := by
    simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (0 : Fin 3)
  have hR1 : M 1 0 + M 1 1 + M 1 2 = 3 * e := by
    simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (1 : Fin 3)
  have hR2 : M 2 0 + M 2 1 + M 2 2 = 3 * e := by
    simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (2 : Fin 3)
  have hD : M 0 0 + M 1 1 + M 2 2 = 3 * e := by
    simpa [diagSum, Fin.sum_univ_three] using hM.2.1
  have hA : M 0 2 + M 1 1 + M 2 0 = 3 * e := by
    simpa [antiDiagSum, Fin.sum_univ_three] using hM.2.2
  have h01 : M 0 1 = M 1 0 := hsym (0 : Fin 3) (1 : Fin 3)
  have h02 : M 0 2 = M 2 0 := hsym (0 : Fin 3) (2 : Fin 3)
  have h12 : M 1 2 = M 2 1 := hsym (1 : Fin 3) (2 : Fin 3)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symmMagic3] <;> omega
