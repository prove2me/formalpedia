-- Prove2me | solution 1 for GlobalTheory.DenseFibreIso.isPullback_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:14.152843+00:00
-- url     : https://prove2.me/submissions/034f2d36-6699-4f10-b29e-8d319b108002

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAwaySurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.DenseFibreIso
variable {R : Type} [CommRing R] {Γ' X : Scheme.{0}} (s : X ⟶ Sp R) (f : Γ' ⟶ X)
namespace GlobalTheory.DenseFibreIso
theorem _root_.solution (A S B : Type) [CommRing A] [CommRing S] [CommRing B] [Algebra A S]
    [Algebra A B] :
    IsPullback (spMap (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] B))
      (spMap (Algebra.TensorProduct.includeRight.toRingHom : B →+* S ⊗[A] B))
      (spMap (algebraMap A S)) (spMap (algebraMap A B)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A S B)
end GlobalTheory.DenseFibreIso
