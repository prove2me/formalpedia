-- Prove2me | solution 1 for GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:03.090209+00:00
-- url     : https://prove2.me/submissions/72b13213-e55a-4b16-8ffe-c6c0e4c7bd4e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks

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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct Pointwise
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {X U : Scheme.{0}} (j : U ⟶ X) [Flat j]
    [SurjectiveOnStalks j] (u : U) : IsIso (j.stalkMap u) := by
  have hs := j.stalkMap_surjective u
  letI := (j.stalkMap u).hom.toAlgebra
  haveI : Module.Flat _ _ := Flat.stalkMap j u
  haveI : IsLocalHom (algebraMap (X.presheaf.stalk (j u)) (U.presheaf.stalk u)) :=
    inferInstanceAs (IsLocalHom (j.stalkMap u).hom)
  haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := X.presheaf.stalk (j u)) (B := U.presheaf.stalk u)
  have hi : Function.Injective (j.stalkMap u).hom :=
    FaithfulSMul.algebraMap_injective (X.presheaf.stalk (j u)) (U.presheaf.stalk u)
  exact (ConcreteCategory.isIso_iff_bijective _).2 ⟨hi, hs⟩
end _root_.GlobalTheory
end GlobalTheory
