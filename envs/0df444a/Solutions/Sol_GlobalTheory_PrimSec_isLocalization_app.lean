-- Prove2me | solution 1 for GlobalTheory.PrimSec.isLocalization_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:56:53.673123+00:00
-- url     : https://prove2.me/submissions/00200b9e-440e-4dc3-9af5-daf8a7ea9b6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingExistsAssociatedOfSumEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulSecNonzeroOnSpecialFibre
import Theorems.Thm_GlobalTheory_PrimSec_isPushout_app
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


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
noncomputable section
open GlobalTheory GlobalTheory.PrimSec
variable {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
  {X XK : Scheme.{0}} {f : X ⟶ Sp O} {j : XK ⟶ X} {fK : XK ⟶ Sp K}
  (H : IsPullback j fK f (spMap (algebraMap O K)))
include H
namespace GlobalTheory.PrimSec
theorem _root_.solution {U : X.Opens} (hU : IsAffineOpen U) :
    letI := (j.app U).hom.toAlgebra
    IsLocalization ((nonZeroDivisors O).map (AbLaw.cst f U)) Γ(XK, j ⁻¹ᵁ U) := by
  have po := isPushout_app H hU
  let := (j.app U).hom.toAlgebra
  let : Algebra O Γ(X, U) := (AbLaw.cst f U).toAlgebra
  let : Algebra K Γ(XK, j ⁻¹ᵁ U) := (AbLaw.cst fK (j ⁻¹ᵁ U)).toAlgebra
  let : Algebra O Γ(XK, j ⁻¹ᵁ U) := ((j.app U).hom.comp (AbLaw.cst f U)).toAlgebra
  have : IsScalarTower O Γ(X, U) Γ(XK, j ⁻¹ᵁ U) := .of_algebraMap_eq' rfl
  have : IsScalarTower O K Γ(XK, j ⁻¹ᵁ U) := .of_algebraMap_eq' congr($(po.w).hom)
  exact (Algebra.isLocalization_iff_isPushout (nonZeroDivisors O) K).mpr (CommRingCat.isPushout_iff_isPushout.mp po)
end GlobalTheory.PrimSec
