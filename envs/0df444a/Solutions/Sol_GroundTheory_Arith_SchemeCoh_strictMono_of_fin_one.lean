-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.strictMono_of_fin_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:51.459805+00:00
-- url     : https://prove2.me/submissions/5e290158-3ef8-49a1-a938-48b40db08d07

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
theorem _root_.solution (j : Fin 1 → ι) : StrictMono j := fun a b hab => by
  rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b] at hab
  exact absurd hab (lt_irrefl _)
end GroundTheory.Arith.SchemeCoh
