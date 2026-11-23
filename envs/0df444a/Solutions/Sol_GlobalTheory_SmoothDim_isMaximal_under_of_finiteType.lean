-- Prove2me | solution 1 for GlobalTheory.SmoothDim.isMaximal_under_of_finiteType
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:43:34.883824+00:00
-- url     : https://prove2.me/submissions/36fd108f-5c16-4efc-9fc5-19cdfa17b2ec

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SmoothDim
namespace GlobalTheory.SmoothDim
theorem _root_.solution (K R B : Type*) [Field K] [CommRing R] [CommRing B]
    [Algebra K R] [Algebra K B] [Algebra R B] [IsScalarTower K R B] [Algebra.FiniteType K B]
    (m : Ideal B) [m.IsMaximal] : (m.under R).IsMaximal := by
  letI := Ideal.Quotient.field m
  haveI : Module.Finite K (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (B ⧸ m)
  haveI : Algebra.IsIntegral R (B ⧸ m) := Algebra.IsIntegral.tower_top K
  have h := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (⊥ : Ideal (B ⧸ m))
  rwa [IsScalarTower.algebraMap_eq R B (B ⧸ m), ← Ideal.comap_comap, Ideal.Quotient.algebraMap_eq,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h
end GlobalTheory.SmoothDim
