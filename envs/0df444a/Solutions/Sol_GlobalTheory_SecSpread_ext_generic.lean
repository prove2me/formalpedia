-- Prove2me | solution 1 for GlobalTheory.SecSpread.ext_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:16:49.549683+00:00
-- url     : https://prove2.me/submissions/75d515ab-885f-49ac-9fd4-21f1646938db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsDenomOfIsAffineOpen
import Theorems.Thm_GlobalTheory_SecSpread_spMap_appTop
import Theorems.Thm_GlobalTheory_ProperFunctions_mem_map_ker_of_app_eq_zero
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
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
open GlobalTheory GlobalTheory.SecSpread
variable {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {X X' : Scheme.{0}} {p : X ⟶ Sp R} {φ : X' ⟶ X} {π : X' ⟶ Sp K}
namespace GlobalTheory.SecSpread
theorem _root_.solution (H : IsPullback φ π p (spMap (algebraMap R K))) [Flat p] {W : X.Opens} {a b : Γ(X, W)}
    (h : ∀ z, φ z ∈ W → gs φ z W a = gs φ z W b) : a = b := by
  have hf : Function.Injective (spMap (algebraMap R K)).appTop.hom := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2 x
    obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2 y
    have := ((spMap_appTop _ x).symm.trans hxy).trans (spMap_appTop _ y)
    rw [IsFractionRing.injective R K
      ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1 this)]
  refine fn_ext fun x hx => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen
  have hle : U ≤ W := hUW
  have e : (φ.app U).hom (resG X hle a) = (φ.app U).hom (resG X hle b) := fn_ext fun z hz => by
    have hz' : φ z ∈ U := hz
    refine (gs_pull (𝟙 X') φ z U hz' _).trans (Eq.trans ?_ (gs_pull (𝟙 X') φ z U hz' _).symm)
    rw [Category.id_comp, gs_res φ z hle hz', gs_res φ z hle hz', h z (hle hz')]
  have h0 := ProperFunctions.mem_map_ker_of_app_eq_zero H hU (resG X hle a - resG X hle b)
    ((map_sub _ _ _).trans (sub_eq_zero.2 e))
  rw [(RingHom.injective_iff_ker_eq_bot _).mp hf, Ideal.map_bot, Ideal.mem_bot, sub_eq_zero] at h0
  exact (gs_res (𝟙 X) x hle hxU a).symm.trans ((congrArg _ h0).trans (gs_res (𝟙 X) x hle hxU b))
end GlobalTheory.SecSpread
