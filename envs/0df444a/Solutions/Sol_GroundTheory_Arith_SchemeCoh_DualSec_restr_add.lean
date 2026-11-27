-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.DualSec.restr_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:44:35.182734+00:00
-- url     : https://prove2.me/submissions/48ec75db-81b5-45fb-afdb-3487ac604ff5

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
variable {P : PMod X}
namespace GroundTheory.Arith.SchemeCoh.DualSec
theorem _root_.solution {U U' : X.Opens} (hU : U' ≤ U) (φ ψ : DualSec P U) :
    restr hU (φ + ψ) = restr hU φ + restr hU ψ := rfl
end GroundTheory.Arith.SchemeCoh.DualSec
