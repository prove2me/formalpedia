-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.mem_ordFrom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:26.176841+00:00
-- url     : https://prove2.me/submissions/5acd5ff9-7fe5-4279-86b9-d597f63c55e5

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
variable [LinearOrder ι]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {n : ℕ} {s : ι} {j : Fin (n + 1) → ι} : j ∈ ordFrom s ↔ StrictMono j ∧ s ≤ j 0 :=
  Iff.rfl
end GroundTheory.Arith.SchemeCoh
