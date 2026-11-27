-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.kaehlerOrd_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:42:42.945823+00:00
-- url     : https://prove2.me/submissions/fd0eaefc-f5ca-4d6e-925d-1f75003eee02

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_KaehlerPlace
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_kaehlerCoeff_smul
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_kaehlerCoeff_ne_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_D_kaehlerUniformizer_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open GroundTheory.FunctionField KaehlerDifferential IntermediateField
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable [IsFunctionField k K]
variable [PerfectField k]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (v : Place k K) {f : K} (hf : f ≠ 0) {ω : Ω[K⁄k]} (hω : ω ≠ 0) :
    kaehlerOrd v (f • ω) = v.ord f + kaehlerOrd v ω := by
  rw [kaehlerOrd, kaehlerCoeff_smul (D_kaehlerUniformizer_ne_zero v),
    v.ord_mul hf (kaehlerCoeff_ne_zero (D_kaehlerUniformizer_ne_zero v) hω), kaehlerOrd]
end GroundTheory.Arith.SchemeCoh
