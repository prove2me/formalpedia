-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.DualSec.dualBasis_app_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:18.597883+00:00
-- url     : https://prove2.me/submissions/5efcf099-4b45-4b76-a6b3-0477404c0737

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory Opposite TensorProduct AlgebraicGeometry TopologicalSpace
universe u
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
variable {X : Scheme.{u}}
open GroundTheory.Arith.SchemeCoh.DualSec
variable {P : PMod X} {U : X.Opens} {s : P.obj (op U)}
namespace GroundTheory.Arith.SchemeCoh.DualSec
theorem _root_.solution (hs : IsBasisOn P U s) (V : X.Opens) (h : V ≤ U) :
    (dualBasis hs).app V h (resM P h s) = 1 := by
  change (coordEquiv hs V h).symm (resM P h s) = 1
  rw [LinearEquiv.symm_apply_eq, coordEquiv_apply, one_smul]
end GroundTheory.Arith.SchemeCoh.DualSec
