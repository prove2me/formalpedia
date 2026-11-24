-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.mem_rangeIn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:02.305859+00:00
-- url     : https://prove2.me/submissions/aaaa0521-b205-4abf-a0b0-6a81ccfb90ec

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains

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
open CategoryTheory
universe w
variable {ι : Type w}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {n : ℕ} {S : Set ι} {j : Fin (n + 1) → ι} : j ∈ rangeIn S ↔ Set.range j ⊆ S :=
  Iff.rfl
end GroundTheory.Arith.SchemeCoh
