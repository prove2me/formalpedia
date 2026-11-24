-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isBasisOn_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:27:47.143455+00:00
-- url     : https://prove2.me/submissions/db3c8ebc-4ad9-4587-b140-5381ba60543c

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ModulesTensor
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_tensorToSheaf_tensorLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [reassoc] GroundTheory.Arith.SchemeCoh.tensorToSheaf_tensorLift

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory Opposite TensorProduct AlgebraicGeometry TopologicalSpace
universe u
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
variable {X : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (U : X.Opens) :
    IsBasisOn ((preMod X).obj (𝟙_ X.Modules)) U (1 : ringOn X U) := by
  intro V h
  have e : resM ((preMod X).obj (𝟙_ X.Modules)) h (1 : ringOn X U) = (1 : ringOn X V) :=
    map_one (resR h)
  simp only [e]
  change Function.Bijective (fun r : ringOn X V => r * 1)
  simp only [mul_one]
  exact Function.bijective_id
end GroundTheory.Arith.SchemeCoh
