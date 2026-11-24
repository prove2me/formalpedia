-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.minIdx_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:28.137316+00:00
-- url     : https://prove2.me/submissions/1999d51a-056f-4cb1-b120-1f8f3d2c8968

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
theorem _root_.solution {n : ℕ} (i : Fin (n + 1) → ι) (a : Fin (n + 1)) : minIdx i ≤ i a :=
  Finset.inf'_le _ (Finset.mem_univ a)
end GroundTheory.Arith.SchemeCoh
