-- Prove2me | solution 1 for N25.unitRelation25_sturm_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:12.757429+00:00
-- url     : https://prove2.me/submissions/fdbdfd9c-3f4a-48f8-a5bc-5079cd8832fa

import Mathlib
import Theorems.Thm_N25_unitRelation25_coefficients_zero_to_thousand
import Definitions.Def_N25_UnitRelationCertificate
import Definitions.Def_Polynomial_BinomialResidue
import Definitions.Def_N25_UnitRelation
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_N25_unitRelation25_coefficients_thousand_to_twoThousand
import Theorems.Thm_N25_unitRelation25_coefficients_twoThousand_to_threeThousand
import Theorems.Thm_N25_unitRelation25_coefficients_threeThousand_to_fourThousand
import Theorems.Thm_N25_unitRelation25_coefficients_fourThousand_to_bound

namespace N25

/-- All coefficients through the weight-396 Sturm bound vanish, including
the endpoint coefficient numbered 4950. -/
theorem _root_.solution :
    ∀ n : Fin 4951, PowerSeries.coeff n.val unitRelationClearedSeries25 = 0 := by
  intro n
  by_cases h₀ : n.val < 1000
  · simpa only [zero_add] using unitRelation25_coefficients_zero_to_thousand ⟨n.val, h₀⟩
  by_cases h₁ : n.val < 2000
  · have h := unitRelation25_coefficients_thousand_to_twoThousand ⟨n.val-1000, by omega⟩
    simpa only [show 1000 + (n.val-1000) = n.val by omega] using h
  by_cases h₂ : n.val < 3000
  · have h := unitRelation25_coefficients_twoThousand_to_threeThousand ⟨n.val-2000, by omega⟩
    simpa only [show 2000 + (n.val-2000) = n.val by omega] using h
  by_cases h₃ : n.val < 4000
  · have h := unitRelation25_coefficients_threeThousand_to_fourThousand ⟨n.val-3000, by omega⟩
    simpa only [show 3000 + (n.val-3000) = n.val by omega] using h
  have h := unitRelation25_coefficients_fourThousand_to_bound ⟨n.val-4000, by omega⟩
  simpa only [show 4000 + (n.val-4000) = n.val by omega] using h

end N25
