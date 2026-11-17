-- Prove2me | solution 1 for N25.unitRelation25_coefficients_zero_to_thousand
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:02:22.205808+00:00
-- url     : https://prove2.me/submissions/d314d0fd-9d90-4125-8bb5-274d5a4fcf4e

import Mathlib
import Theorems.Thm_N25_unitRelationNumeratorPolynomial25_coefficients
import Definitions.Def_N25_UnitRelationCertificate
import Definitions.Def_Polynomial_BinomialResidue
import Theorems.Thm_N25_unitRelationClearedSeries25_coefficients_of_polynomial
import Definitions.Def_N25_UnitRelation
import Definitions.Def_N25_UnitSeries

namespace N25

/-- The cleared coefficient certificate on the interval [0, 1000). -/
theorem _root_.solution :
    ∀ n : Fin 1000, PowerSeries.coeff (0 + n.val) unitRelationClearedSeries25 = 0 := by
  intro n
  exact unitRelationClearedSeries25_coefficients_of_polynomial 4951 199
    (by norm_num) unitRelationNumeratorPolynomial25_coefficients _ (by omega)

end N25
