-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.lin_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:02.311813+00:00
-- url     : https://prove2.me/submissions/b6fafb2f-84a7-4f6d-b98d-d0f995753295

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
theorem _root_.solution {m n : ℕ} (f : (Fin (m + 1) → ι) → Chain ι n) (j : Fin (m + 1) → ι) (z : ℤ) :
    lin f (Finsupp.single j z) = z • f j := by
  rw [lin, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply]
end GroundTheory.Arith.SchemeCoh
