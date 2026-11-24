-- Prove2me | solution 1 for GlobalTheory.Phase.GaussSum.quat_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:26:00.911961+00:00
-- url     : https://prove2.me/submissions/fb2d6e6b-408a-4b42-93d1-c547641cb9e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsZeroOrPosMulRootOfUnityFiniteGaussSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.GaussSum
namespace GlobalTheory.Phase.GaussSum
theorem _root_.solution {M W : Type} [AddCommGroup M] [AddCommGroup W] (β : M →+ M →+ W) (a b c d : ℤ)
    (x y : Fin 4 → M) :
    ∑ i, β (quat a b c d x i) (quat a b c d y i) =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • ∑ i, β (x i) (y i) := by
  simp only [Fin.sum_univ_four, quat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    map_add, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply]
  module
end GlobalTheory.Phase.GaussSum
