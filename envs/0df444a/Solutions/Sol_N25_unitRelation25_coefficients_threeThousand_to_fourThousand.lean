-- Prove2me | solution 1 for N25.unitRelation25_coefficients_threeThousand_to_fourThousand
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:02:20.999678+00:00
-- url     : https://prove2.me/submissions/da896239-fe3a-435a-be71-1a0c0e46f2c4

import Mathlib
import Theorems.Thm_N25_unitRelationNumeratorPolynomial25_coefficients
import Definitions.Def_N25_UnitRelationCertificate
import Definitions.Def_Polynomial_BinomialResidue
import Theorems.Thm_N25_unitRelationClearedSeries25_coefficients_of_polynomial
import Definitions.Def_N25_UnitRelation
import Definitions.Def_N25_UnitSeries

namespace N25

/-- The cleared coefficient certificate on the interval [3000, 4000). -/
theorem _root_.solution :
    ∀ n : Fin 1000, PowerSeries.coeff (3000 + n.val) unitRelationClearedSeries25 = 0 := by
  intro n
  exact unitRelationClearedSeries25_coefficients_of_polynomial 4951 199
    (by norm_num) unitRelationNumeratorPolynomial25_coefficients _ (by omega)

end N25
