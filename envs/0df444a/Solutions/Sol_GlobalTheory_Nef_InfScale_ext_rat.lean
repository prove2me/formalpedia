-- Prove2me | solution 1 for GlobalTheory.Nef.InfScale.ext_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:01:55.74549+00:00
-- url     : https://prove2.me/submissions/4e552a48-3eeb-4caa-afb8-645b246edb0f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsScalingCompatibleExpansionAtInfinity
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.InfScale
variable {F : Type} [Field F]
namespace GlobalTheory.Nef.InfScale
theorem _root_.solution {A : Type} [CommRing A] {f g : RatFunc F →+* A}
    (hC : ∀ a, f (RatFunc.C a) = g (RatFunc.C a)) (hX : f RatFunc.X = g RatFunc.X) : f = g := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors F[X])
  apply Polynomial.ringHom_ext
  · intro a; simpa [RatFunc.algebraMap_C] using hC a
  · simpa [RatFunc.algebraMap_X] using hX
end GlobalTheory.Nef.InfScale
