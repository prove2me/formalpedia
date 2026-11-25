-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.CechOrdered.Supp.sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:38.016942+00:00
-- url     : https://prove2.me/submissions/40a96a36-e4f1-4649-8263-72fe034db7bd

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_Supp_neg

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
theorem _root_.solution {z z' : Chain ι q} (hz : Supp Q z) (hz' : Supp Q z') : Supp Q (z - z') := by
  rw [sub_eq_add_neg]
  exact hz.add hz'.neg
end Supp
end GroundTheory.Arith.SchemeCoh.CechOrdered
