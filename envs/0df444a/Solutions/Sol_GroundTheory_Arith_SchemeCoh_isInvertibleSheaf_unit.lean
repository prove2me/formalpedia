-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isInvertibleSheaf_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:47:04.64424+00:00
-- url     : https://prove2.me/submissions/95c6f56c-a147-49cf-b495-788952658c98

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ModulesTensor
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isBasisOn_one

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
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution : IsInvertibleSheaf (𝟙_ X.Modules) :=
  fun _ => ⟨⊤, trivial, (1 : ringOn X ⊤), isBasisOn_one ⊤⟩
end GroundTheory.Arith.SchemeCoh
