-- Prove2me | solution 1 for GlobalTheory.SecSpread.exists_denom_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:24:10.290642+00:00
-- url     : https://prove2.me/submissions/a950dc90-a441-4877-b328-bf431287052f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsDenomOfIsAffineOpen
import Theorems.Thm_GlobalTheory_SecSpread_exists_denom_of_isPushout
import Theorems.Thm_GlobalTheory_SecSpread_spMap_appTop
import Theorems.Thm_GlobalTheory_ProperFunctions_appLE_top_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
open GlobalTheory GlobalTheory.SecSpread
variable {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {X X' : Scheme.{0}} {p : X ⟶ Sp R} {φ : X' ⟶ X} {π : X' ⟶ Sp K}
namespace GlobalTheory.SecSpread
theorem _root_.solution (H : IsPullback φ π p (spMap (algebraMap R K))) {U : X.Opens}
    (hU : IsAffineOpen U) (t : Γ(X', φ ⁻¹ᵁ U)) :
    ∃ d : R, d ≠ 0 ∧ ∃ a : Γ(X, U), (φ.app U).hom (constFn p U d) * t = (φ.app U).hom a := by
  have := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := U)
    (UY := φ ⁻¹ᵁ U) (ProperFunctions.le_preimage_top _ ⊤) (ProperFunctions.le_preimage_top p U) (by simp)
    (isAffineOpen_top _) (isAffineOpen_top _) hU
  have h := (isIso_pushoutSection_iff ..).mp this
  rw [ProperFunctions.appLE_top_top, Scheme.Hom.appLE_eq_app] at h
  refine exists_denom_of_isPushout h (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (fun k => ?_) t
  obtain ⟨k, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2 k
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) k
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨b, hb0, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a, ?_⟩
  rw [spMap_appTop, spMap_appTop, ← map_mul]
  congr 1
  exact mul_div_cancel₀ _ ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hb0)
end GlobalTheory.SecSpread
