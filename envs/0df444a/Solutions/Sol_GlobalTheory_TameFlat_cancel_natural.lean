-- Prove2me | solution 1 for GlobalTheory.TameFlat.cancel_natural
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:34:12.41927+00:00
-- url     : https://prove2.me/submissions/5d95dd40-227f-4410-8816-b0b264e97550

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FlatOfTameDescent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.TameFlat
open TensorProduct
namespace GlobalTheory.TameFlat
theorem _root_.solution {A B R X Y : Type} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup R] [Module A R]
    [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X]
    [AddCommGroup Y] [Module A Y] [Module B Y] [IsScalarTower A B Y]
    (f : X →ₗ[B] Y) (t : X ⊗[B] (B ⊗[A] R)) :
    AlgebraTensorModule.cancelBaseChange A B B Y R (f.rTensor _ t) =
      (f.restrictScalars A).rTensor R (AlgebraTensorModule.cancelBaseChange A B B X R t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c r =>
      simp only [LinearMap.rTensor_tmul, AlgebraTensorModule.cancelBaseChange_tmul,
        LinearMap.restrictScalars_apply, map_smul]
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
  | add s u hs hu => simp only [map_add, hs, hu]
end GlobalTheory.TameFlat
