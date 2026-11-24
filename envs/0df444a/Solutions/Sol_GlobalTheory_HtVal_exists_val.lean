-- Prove2me | solution 1 for GlobalTheory.HtVal.exists_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:55:14.444804+00:00
-- url     : https://prove2.me/submissions/84cc25a9-fcc4-42a6-80ae-1c9fb6a56fde

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_MemRangeOfForallHeightOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocalizationAtPrimeIsDiscreteValuationRingOfHeig
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHeightOneValuationsControlSubgroup
import Theorems.Thm_GlobalTheory_HtVal_dvr_val
import Theorems.Thm_GlobalTheory_localizationAtPrime_isDiscreteValuationRing_of_height_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HtVal
namespace GlobalTheory.HtVal
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (P : Ideal R) [P.IsPrime] (h1 : P.height = 1) :
    ∃ w : (FractionRing R)ˣ →* Multiplicative ℤ, ∀ x : (FractionRing R)ˣ,
      0 ≤ Multiplicative.toAdd (w x) ↔
        ∃ s ∉ P, algebraMap R (FractionRing R) s * x ∈ (algebraMap R (FractionRing R)).range := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one R P h1
  obtain ⟨w, hw⟩ := dvr_val (Localization.AtPrime P) (FractionRing R)
  refine ⟨w, fun x => (hw x).trans ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy⟩
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj P.primeCompl y
    refine ⟨s, s.2, r, ?_⟩
    have := congrArg (algebraMap (Localization.AtPrime P) (FractionRing R)) hrs
    simp only [map_mul, ← IsScalarTower.algebraMap_apply] at this
    rw [← this, hy, mul_comm]
  · rintro ⟨s, hs, r, hr⟩
    refine ⟨IsLocalization.mk' (Localization.AtPrime P) r (⟨s, hs⟩ : P.primeCompl), ?_⟩
    have hs0 : algebraMap R (FractionRing R) s ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))]
      rintro rfl; exact hs P.zero_mem
    apply mul_left_cancel₀ hs0
    rw [← hr, IsScalarTower.algebraMap_apply R (Localization.AtPrime P) (FractionRing R) s,
      IsScalarTower.algebraMap_apply R (Localization.AtPrime P) (FractionRing R) r, ← map_mul]
    congr 1
    rw [mul_comm]
    exact IsLocalization.mk'_spec (Localization.AtPrime P) r (⟨s, hs⟩ : P.primeCompl)
end GlobalTheory.HtVal
