-- Prove2me | solution 1 for GlobalTheory.GenericSpread.exists_away_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:59:18.036326+00:00
-- url     : https://prove2.me/submissions/5af4504e-a782-4fd9-b73e-0de036282c8a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MorphismsGenericSpreadOut
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
open GlobalTheory GlobalTheory.GenericSpread
namespace GlobalTheory.GenericSpread
theorem _root_.solution {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (S : Subalgebra R K) (hS : S.FG) :
    ∃ (f : R) (_ : f ≠ 0) (g : S →ₐ[R] Localization.Away f) (l : Localization.Away f →ₐ[R] K),
      ∀ x, l (g x) = x := by
  classical
  obtain ⟨t, rfl⟩ := hS
  choose p hp using fun x : K => IsLocalization.surj (nonZeroDivisors R) x
  set f : R := ∏ x ∈ t, ((p x).2 : R) with hf_def
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x _ => nonZeroDivisors.ne_zero (p x).2.2
  have hfK : IsUnit (algebraMap R K f) :=
    ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hf0).isUnit
  have hpow : ∀ y : Submonoid.powers f, IsUnit (algebraMap R K y) := by
    rintro ⟨_, n, rfl⟩
    simpa using hfK.pow n
  let l : Localization.Away f →ₐ[R] K :=
    ⟨IsLocalization.lift (M := Submonoid.powers f) (S := Localization.Away f) hpow,
      fun r => IsLocalization.lift_eq hpow r⟩
  have hl : Function.Injective l := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) z
    have h1 := congrArg l (IsLocalization.mk'_spec (Localization.Away f) a s)
    rw [map_mul, hz, zero_mul, AlgHom.commutes] at h1
    have ha : a = 0 := (IsFractionRing.injective R K) (by rw [← h1, map_zero])
    subst ha
    exact IsLocalization.mk'_zero s
  have hle : Algebra.adjoin R (↑t : Set K) ≤ l.range := by
    rw [Algebra.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, AlgHom.mem_range]
    have hdvd : ((p x).2 : R) ∣ f := Finset.dvd_prod_of_mem _ (Finset.mem_coe.mp hx)
    have hu : IsUnit (algebraMap R (Localization.Away f) ((p x).2 : R)) :=
      isUnit_of_dvd_unit (map_dvd _ hdvd) (IsLocalization.Away.algebraMap_isUnit f)
    refine ⟨algebraMap R _ (p x).1 * ↑hu.unit⁻¹, ?_⟩
    have hne : algebraMap R K ((p x).2 : R) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero (p x).2.2)
    apply mul_right_cancel₀ hne
    calc l (algebraMap R _ (p x).1 * ↑hu.unit⁻¹) * algebraMap R K ((p x).2 : R)
        = l (algebraMap R _ (p x).1 * ↑hu.unit⁻¹ * algebraMap R _ ((p x).2 : R)) := by
          rw [map_mul l _ (algebraMap R _ _), AlgHom.commutes]
      _ = l (algebraMap R _ (p x).1) := by rw [_root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]
      _ = algebraMap R K (p x).1 := AlgHom.commutes l _
      _ = x * algebraMap R K ((p x).2 : R) := (hp x).symm
  refine ⟨f, hf0, (AlgEquiv.ofInjective l hl).symm.toAlgHom.comp (Subalgebra.inclusion hle), l,
    fun x => ?_⟩
  show l ((AlgEquiv.ofInjective l hl).symm (Subalgebra.inclusion hle x)) = x
  rw [← AlgEquiv.ofInjective_apply l hl, AlgEquiv.apply_symm_apply]
  rfl
end GlobalTheory.GenericSpread
