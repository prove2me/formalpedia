-- Prove2me | solution 1 for GlobalTheory.PrimSec.exists_numerator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:29:18.74891+00:00
-- url     : https://prove2.me/submissions/2319e7e1-f6a7-4e56-bff5-f3623f5da7bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingExistsAssociatedOfSumEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulSecNonzeroOnSpecialFibre
import Theorems.Thm_GlobalTheory_PrimSec_app_cst
import Theorems.Thm_GlobalTheory_PrimSec_isLocalization_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
theorem _root_.solution {U : X.Opens} (hU : IsAffineOpen U) (t : Γ(XK, j ⁻¹ᵁ U)) :
    ∃ (π : O) (b : Γ(X, U)), π ≠ 0 ∧ (j.app U).hom b = AbLaw.cst fK (j ⁻¹ᵁ U) (algebraMap O K π) * t := by
  letI := (j.app U).hom.toAlgebra
  haveI := isLocalization_app H hU
  obtain ⟨⟨b, _, π, hπ, rfl⟩, h⟩ := IsLocalization.surj ((nonZeroDivisors O).map (AbLaw.cst f U)) t
  refine ⟨π, b, nonZeroDivisors.ne_zero hπ, ?_⟩
  rw [← app_cst H.w, mul_comm]
  exact h.symm
end GlobalTheory.PrimSec
