-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.map_top_eq_fieldRange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:33:32.915711+00:00
-- url     : https://prove2.me/submissions/2432dd7d-66bf-46ec-aad4-3202612dc6be

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some



set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
universe u
variable {F : Type u} [Field F]
variable (E : WeierstrassCurve F) [E.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {K L : Type*} [Field K] [Field L] [Algebra F K] [Algebra F L]
    (f : K →ₐ[F] L) : (⊤ : IntermediateField F K).map f = f.fieldRange := by
  ext z
  simp only [IntermediateField.mem_map, IntermediateField.mem_top, true_and, AlgHom.mem_fieldRange]
end GroundTheory.Arith.Abelian
