-- Prove2me | solution 1 for GlobalTheory.GenericSmooth.finrank_derivation_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:17:31.824329+00:00
-- url     : https://prove2.me/submissions/fc83808a-e849-482e-b6a8-edd26a997f6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothGenericFibreOfIndependentAndTangentBound

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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.GenericSmooth
namespace GlobalTheory.GenericSmooth
theorem _root_.solution (o k R S C : Type) [CommRing o] [CommRing k]
    [CommRing R] [CommRing S] [Field C] [Algebra o k] [Algebra o R] [Algebra k S]
    [Algebra R S] [Algebra o S] [IsScalarTower o R S] [IsScalarTower o k S]
    (M : Submonoid R) [IsLocalization M S] [Algebra.FiniteType o R]
    [Algebra k C] [Algebra S C] [IsScalarTower k S C] [Algebra o C] [Algebra R C]
    [IsScalarTower o R C] [IsScalarTower R S C] [IsScalarTower o S C] [IsScalarTower o k C] :
    Module.finrank C (Derivation k S C) ≤ Module.finrank C (Derivation o R C) := by
  have : Module.Finite C (Derivation o R C) :=
    Module.Finite.equiv (GlobalTheory.SmoothTangent.derivationEquivDual o R C).symm
  let f : Derivation k S C →ₗ[C] Derivation o R C :=
    { toFun := fun D ↦ (D.restrictScalars o).compAlgebraMap R
      map_add' := fun _ _ ↦ by ext; rfl
      map_smul' := fun _ _ ↦ by ext; rfl }
  refine LinearMap.finrank_le_finrank_of_injective (f := f) ?_
  rw [injective_iff_map_eq_zero]
  intro D hD
  have h0 : ∀ r, D (algebraMap R S r) = 0 := fun r ↦ congr($hD r)
  ext s
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj M s
  have := congrArg D hab
  rw [D.leibniz, h0, h0, smul_zero, zero_add, Algebra.smul_def] at this
  exact (mul_eq_zero.mp this).resolve_left
    ((IsLocalization.map_units S b).map (algebraMap S C)).ne_zero
end GlobalTheory.GenericSmooth
