-- Prove2me | solution 1 for ModularCurve.fibrePoly_eq_of_kroneckerCongruence
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/ed4abf08-3210-525a-bd76-7a19a5029e91

import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_fibrePoly_eq_of_kroneckerCongruence
open Polynomial ModularCurve
theorem solution {k : Type*} [Field k]
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ] (data : ModularCurve.ModularPolynomialData ℓ)
    (hK : ModularCurve.KroneckerCongruence ℓ data) (a : k) :
    ModularCurve.fibrePoly data.Φ a =
      (Polynomial.C (a ^ ℓ) - Polynomial.X) * (Polynomial.C a - Polynomial.X ^ ℓ) := by
  have hK' : reduceModBivar ℓ data.Φ =
      (Polynomial.C Polynomial.X ^ ℓ - Polynomial.X) *
        (Polynomial.C Polynomial.X - Polynomial.X ^ ℓ) := hK
  rw [fibrePoly_eq_map_reduceModBivar (ℓ := ℓ), hK']
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, map_pow]

end S_ModularCurve_fibrePoly_eq_of_kroneckerCongruence
end P2MW
export P2MW.S_ModularCurve_fibrePoly_eq_of_kroneckerCongruence (solution)
