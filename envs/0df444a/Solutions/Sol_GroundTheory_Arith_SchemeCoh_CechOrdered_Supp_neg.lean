-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.CechOrdered.Supp.neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:45:34.302448+00:00
-- url     : https://prove2.me/submissions/18352322-7bed-4526-bfc5-f8544d49b904

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe w u
open GroundTheory.Arith.SchemeCoh.CechOrdered
variable (ι : Type w)
variable {ι}
variable {q : ℕ} {Q Q' : (Fin (q + 1) → ι) → Prop}
namespace GroundTheory.Arith.SchemeCoh.CechOrdered
namespace Supp
theorem _root_.solution {z : Chain ι q} (hz : Supp Q z) : Supp Q (-z) := by
  simpa using hz.smul (-1)
end Supp
end GroundTheory.Arith.SchemeCoh.CechOrdered
