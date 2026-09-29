-- Prove2me | solution 1 for ModularCurve.frobenius_identity_lambda
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/83b7de5d-28f2-5ccf-bedf-ab324666b9e5

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Theorems.Thm_ModularCurve_pow_char_eq_map_frobenius_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_frobenius_identity_lambda

set_option autoImplicit false

open ModularCurve

theorem solution (K : Type*) [CommRing K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] :
    lambdaNModC K ℓ = (lambdaModC K) ^ ℓ := by
  rw [lambdaNModC, lambdaModC, pow_char_eq_map_frobenius_qExpand ℓ]
  change _ = laurentMap (frobenius K ℓ) (qExpand K ℓ (laurentMap (Int.castRingHom K) lambdaInt))
  rw [laurentMap_qExpand, laurentMap_laurentMap]
  have hcomp : (frobenius K ℓ).comp (Int.castRingHom K) = Int.castRingHom K := RingHom.ext_int _ _
  rw [hcomp]

end S_ModularCurve_frobenius_identity_lambda
end P2MW
export P2MW.S_ModularCurve_frobenius_identity_lambda (solution)
