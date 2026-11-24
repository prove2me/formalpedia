-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.cone_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:27.043573+00:00
-- url     : https://prove2.me/submissions/e2946d65-82f0-4a75-985b-7f7c0d99dfaf

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
theorem _root_.solution {n : ℕ} (s : ι) (i : Fin (n + 1) → ι) (z : ℤ) :
    cone s (Finsupp.single i z) = Finsupp.single (Fin.cons s i : Fin (n + 2) → ι) z :=
  Finsupp.mapDomain_single
end GroundTheory.Arith.SchemeCoh
