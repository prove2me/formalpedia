-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.tensorBasisMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:00:25.833003+00:00
-- url     : https://prove2.me/submissions/a96152b6-d385-412f-8832-1cd56d791a64

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_QcohLocal
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_IsQuasicoherentTensorOfInvertible

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
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
universe u
noncomputable section
variable {X : Scheme.{u}}
variable {M M' L : X.Modules} {U V : X.Opens} {s : ((preMod X).obj L).obj (op U)}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (h : V ≤ U) (m : Γ(M, V)) :
    tensorBasisMap M L s h m = (tensorToSheaf M L).app (op V)
      ((show ((preMod X).obj M).obj (op V) from m) ⊗ₜ resM ((preMod X).obj L) h s :
        ((preMod X).obj M ⊗ (preMod X).obj L).obj (op V)) := rfl
end GroundTheory.Arith.SchemeCoh
