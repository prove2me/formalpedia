-- Prove2me | solution 1 for N25.unitRelation25_coefficients_fourThousand_to_bound
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:59:14.837044+00:00
-- url     : https://prove2.me/submissions/c91925b3-5452-4758-95fa-90dcb24d46cd

import Mathlib
import Theorems.Thm_N25_unitRelationNumeratorPolynomial25_coefficients
import Definitions.Def_N25_UnitRelationCertificate
import Definitions.Def_Polynomial_BinomialResidue
import Theorems.Thm_N25_unitRelationClearedSeries25_coefficients_of_polynomial
import Definitions.Def_N25_UnitRelation
import Definitions.Def_N25_UnitSeries

namespace N25

/-- The cleared coefficient certificate on the interval [4000, 4951). -/
theorem _root_.solution :
    ∀ n : Fin 951, PowerSeries.coeff (4000 + n.val) unitRelationClearedSeries25 = 0 := by
  intro n
  exact unitRelationClearedSeries25_coefficients_of_polynomial 4951 199
    (by norm_num) unitRelationNumeratorPolynomial25_coefficients _ (by omega)

end N25
