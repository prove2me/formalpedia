-- Prove2me | solution 1 for GlobalTheory.TorusNil.ringHom_ext_int_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:46:12.288434+00:00
-- url     : https://prove2.me/submissions/e1b45409-f4d8-40fb-b98b-17d55a80294e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Theorems.Thm_GlobalTheory_TorusNil_ringHom_uliftInt_ext

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
theorem _root_.solution {C : Type} [Semiring C]
    {f g : AddMonoidAlgebra (ULift.{0} ℤ) X →+* C}
    (h : ∀ y, f (AddMonoidAlgebra.single y 1) = g (AddMonoidAlgebra.single y 1)) : f = g :=
  AddMonoidAlgebra.ringHom_ext (fun r => RingHom.congr_fun
    (ringHom_uliftInt_ext (f.comp AddMonoidAlgebra.singleZeroRingHom)
      (g.comp AddMonoidAlgebra.singleZeroRingHom)) r) h
end GlobalTheory.TorusNil
