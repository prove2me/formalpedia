-- Prove2me | solution 1 for GlobalTheory.DegKer.finrank_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:06:00.436879+00:00
-- url     : https://prove2.me/submissions/f06a3cdb-cc86-4b25-817b-25d00125f49b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MapDegreeEqExpCharPowMulCardKernel
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_GlobalTheory_ZV_ActsBy_comp
import Theorems.Thm_GlobalTheory_ZV_MapDeg_finrank_eq


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
open GlobalTheory.ZV
noncomputable section
open GlobalTheory
open GlobalTheory.DegKer
namespace GlobalTheory.DegKer
theorem _root_.solution {R S R' S' : Type} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsDomain R] [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] (f : R) (hf : f ≠ 0)
    [IsLocalization.Away f R'] [IsLocalization.Away (algebraMap R S f) S']
    (h : (algebraMap R' S').comp (algebraMap R R') = (algebraMap S S').comp (algebraMap R S)) :
    Module.finrank R' S' = Module.finrank R S := by
  letI : Algebra R S' := ((algebraMap S S').comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq' h.symm
  have hle : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers f)) S' := by
    rw [Algebra.algebraMapSubmonoid_powers]; infer_instance
  haveI : IsLocalizedModule (Submonoid.powers f) (IsScalarTower.toAlgHom R S S').toLinearMap :=
    (isLocalizedModule_iff_isLocalization).mpr this
  rw [IsLocalization.finrank_eq R' (Submonoid.powers f) hle,
    IsLocalizedModule.finrank_eq (Submonoid.powers f) (IsScalarTower.toAlgHom R S S').toLinearMap hle]
end GlobalTheory.DegKer
