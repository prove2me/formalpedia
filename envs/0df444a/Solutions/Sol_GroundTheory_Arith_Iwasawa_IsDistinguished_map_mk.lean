-- Prove2me | solution 1 for GroundTheory.Arith.Iwasawa.IsDistinguished.map_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:43:27.500999+00:00
-- url     : https://prove2.me/submissions/e8f68016-659b-4a21-80f4-c7b4137089ae

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_IwasawaModules_SpanFinrankMaximalIdealLeTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Iwasawa
open PowerSeries IsLocalRing
open scoped Polynomial
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
namespace GroundTheory.Arith.Iwasawa
namespace IsDistinguished
theorem _root_.solution {P : ℤ_[p][X]} (hP : IsDistinguished p P) :
    (P : Lambda p).map (Ideal.Quotient.mk (maximalIdeal ℤ_[p])) = X ^ P.natDegree := by
  rw [← Polynomial.polynomial_map_coe, Polynomial.IsDistinguishedAt.map_eq_X_pow hP,
    Polynomial.coe_pow, Polynomial.coe_X]
end IsDistinguished
end GroundTheory.Arith.Iwasawa
