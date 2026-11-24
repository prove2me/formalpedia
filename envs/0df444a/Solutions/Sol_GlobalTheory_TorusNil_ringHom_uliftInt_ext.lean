-- Prove2me | solution 1 for GlobalTheory.TorusNil.ringHom_uliftInt_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:33:57.469912+00:00
-- url     : https://prove2.me/submissions/3e10b009-7b13-4526-bbd6-cd718c44d318

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TorusNil
variable {A : Type} [CommRing A]
variable (A) (X : Type) [AddCommGroup X]
namespace GlobalTheory.TorusNil
theorem _root_.solution {C : Type} [Semiring C] (f g : ULift.{0} ℤ →+* C) : f = g := by
  have h := RingHom.ext_int (f.comp (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ).symm.toRingHom)
    (g.comp (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ).symm.toRingHom)
  ext ⟨n⟩
  exact RingHom.congr_fun h n
end GlobalTheory.TorusNil
