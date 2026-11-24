-- Prove2me | solution 1 for GroundTheory.Arith.Iwasawa.IsDistinguished.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:36.060834+00:00
-- url     : https://prove2.me/submissions/5a4278c7-9440-4a6e-a26d-0d124815baf4

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
theorem _root_.solution {P Q : ℤ_[p][X]} (hP : IsDistinguished p P)
    (hQ : IsDistinguished p Q) : IsDistinguished p (P * Q) :=
  Polynomial.IsDistinguishedAt.mul hP hQ
end IsDistinguished
end GroundTheory.Arith.Iwasawa
