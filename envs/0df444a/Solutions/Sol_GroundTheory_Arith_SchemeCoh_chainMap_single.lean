-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.chainMap_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:46:54.760389+00:00
-- url     : https://prove2.me/submissions/a10b7215-47af-4b70-a290-5621674926ff

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
theorem _root_.solution {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) (i : Fin (n + 1) → ι) (z : ℤ) :
    chainMap θ (Finsupp.single i z) = Finsupp.single (i ∘ θ) z :=
  Finsupp.mapDomain_single
end GroundTheory.Arith.SchemeCoh
