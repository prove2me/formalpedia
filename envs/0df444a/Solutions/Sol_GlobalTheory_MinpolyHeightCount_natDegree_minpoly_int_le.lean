-- Prove2me | solution 1 for GlobalTheory.MinpolyHeightCount.natDegree_minpoly_int_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:58:22.00728+00:00
-- url     : https://prove2.me/submissions/d90e68d6-8213-4f16-829d-f9f285f80848

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteAndNcardMinpolyCoeffHeightLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open GlobalTheory GlobalTheory.MinpolyHeightCount
variable (K : Type) [Field K] [NumberField K]
namespace GlobalTheory.MinpolyHeightCount
theorem _root_.solution {x : K} (hx : IsIntegral ℤ x) :
    (minpoly ℤ x).natDegree ≤ Module.finrank ℚ K := by
  rw [← (minpoly.monic hx).natDegree_map (algebraMap ℤ ℚ),
    ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx]
  exact minpoly.natDegree_le x
end GlobalTheory.MinpolyHeightCount
