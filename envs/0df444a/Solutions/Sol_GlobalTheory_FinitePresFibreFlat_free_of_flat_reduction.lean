-- Prove2me | solution 1 for GlobalTheory.FinitePresFibreFlat.free_of_flat_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:13:25.150459+00:00
-- url     : https://prove2.me/submissions/e727e4d2-7cae-4eae-9541-b26982a1cf99

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatOfIsFiniteOfFlatGeometricFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FlatOfIsFiniteOfFinitePresentationOfFlatGeometri
import Theorems.Thm_GlobalTheory_FiniteFibreFlat_lTensor_map_injective
import Theorems.Thm_GlobalTheory_LocalFlat_relationsLift_of_flat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
open GlobalTheory.FinitePresFibreFlat
open TensorProduct IsLocalRing FiniteFibreFlat
namespace GlobalTheory.FinitePresFibreFlat
theorem _root_.solution {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Flat R M]
    [Module.FinitePresentation A M] (p : Ideal R) (hp : p.map (algebraMap R A) ≤ maximalIdeal A)
    [Module.Flat (A ⧸ p.map (algebraMap R A)) ((A ⧸ p.map (algebraMap R A)) ⊗[A] M)] :
    Module.Free A M := by
  set I := p.map (algebraMap R A) with hI
  have hrel : LocalFlat.RelationsLift I M :=
    LocalFlat.relationsLift_of_flat (C := A ⧸ I) Ideal.Quotient.mk_surjective Ideal.mk_ker
      (TensorProduct.mk A (A ⧸ I) M 1) (TensorProduct.mk_surjective A M (A ⧸ I)
        Ideal.Quotient.mk_surjective) (LinearMap.ker_tensorProductMk M)
  apply Module.free_of_maximalIdeal_rTensor_injective
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj, injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hrel (maximalIdeal A) (maximalIdeal A).subtype x (by rw [hx]; simp)
  let e := Submodule.comapSubtypeEquivOfLe hp
  have hy : I.subtype.lTensor M (e.toLinearMap.lTensor M y) = 0 := by
    rw [← hx, ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply]
    rfl
  rw [map_eq_zero_iff _ (lTensor_map_injective p)] at hy
  have : y = 0 := (LinearEquiv.lTensor M e).injective (hy.trans (map_zero _).symm)
  rw [this, map_zero]
end GlobalTheory.FinitePresFibreFlat
