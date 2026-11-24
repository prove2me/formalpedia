-- Prove2me | solution 1 for GroundTheory.Arith.Iwasawa.IsDistinguished.monic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:45:41.150208+00:00
-- url     : https://prove2.me/submissions/f64138de-7f0f-410d-bda9-c25c9391d6ba

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
theorem _root_.solution {P : ℤ_[p][X]} (hP : IsDistinguished p P) : P.Monic :=
  Polynomial.IsDistinguishedAt.monic hP
end IsDistinguished
end GroundTheory.Arith.Iwasawa
