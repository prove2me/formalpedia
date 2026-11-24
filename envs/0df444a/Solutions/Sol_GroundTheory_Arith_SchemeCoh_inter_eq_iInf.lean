-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.inter_eq_iInf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:47.379884+00:00
-- url     : https://prove2.me/submissions/d261fb80-3443-467e-988a-c30a1f0a91c1

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_AffineVanishing
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated

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
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
universe w w' u
variable {X : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {ι : Type w} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) :
    inter (X := X.toTopCat) U i = ⨅ a, U (i a) :=
  SetLike.ext fun x => by
    rw [mem_inter_iff, ← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
    rfl
end GroundTheory.Arith.SchemeCoh
