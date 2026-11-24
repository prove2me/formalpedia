-- Prove2me | solution 1 for GlobalTheory.unitMultiple_descends_of_height_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:39:40.62365+00:00
-- url     : https://prove2.me/submissions/3885a6db-e190-4737-a39f-f5b54c857ee1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalUnitOfDvrUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    (𝔭 : PrimeSpectrum A),
    𝔭.asIdeal.height = 1 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (iT : Localization.AtPrime 𝔭.asIdeal →+* V), Function.Injective iT → IsLocalHom iT →
    ∀ a b : A,
    (∃ w : Vˣ, iT (algebraMap A _ a) = iT (algebraMap A _ b) * w) →
    ∃ u : (Localization.AtPrime 𝔭.asIdeal)ˣ,
      (u : Localization.AtPrime 𝔭.asIdeal) * algebraMap A _ b = algebraMap A _ a := by
  intro A _ _ _ _ 𝔭 h1 V _ _ _ iT hinj hloc a b ⟨w, hw⟩
  haveI : IsDomain (Localization.AtPrime 𝔭.asIdeal) :=
    IsLocalization.isDomain_localization 𝔭.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing (Localization.AtPrime 𝔭.asIdeal) :=
    isDiscreteValuationRing_of_height_eq_one 𝔭.asIdeal h1 _
  set x := algebraMap A (Localization.AtPrime 𝔭.asIdeal) a with hxdef
  set y := algebraMap A (Localization.AtPrime 𝔭.asIdeal) b with hydef
  have hw0 : (w : V) ≠ 0 := w.ne_zero
  by_cases hx : x = 0
  · refine ⟨1, ?_⟩
    have h0 : iT y * (w : V) = 0 := by rw [← hw, hx, map_zero]
    have hy : iT y = 0 := (mul_eq_zero.mp h0).resolve_right hw0
    have : y = 0 := hinj (by rw [hy, map_zero])
    rw [this, hx, mul_zero]
  · have hxT : iT x ≠ 0 := fun h => hx (hinj (by rw [h, map_zero]))
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond x y
    · have e : iT x * (iT c * (w : V)) = iT x * 1 := by
        rw [mul_one, ← mul_assoc, ← map_mul, hc]
        exact hw.symm
      have hcw : iT c * (w : V) = 1 := mul_left_cancel₀ hxT e
      have hc' : IsUnit c := (isUnit_map_iff iT c).mp (IsUnit.of_mul_eq_one _ hcw)
      refine ⟨hc'.unit⁻¹, ?_⟩
      rw [← hc, mul_left_comm, IsUnit.val_inv_mul, mul_one]
    · have hy : y ≠ 0 := by
        rintro h
        apply hx
        rw [← hc, h, zero_mul]
      have hyT : iT y ≠ 0 := fun h => hy (hinj (by rw [h, map_zero]))
      have e : iT y * iT c = iT y * (w : V) := by
        rw [← map_mul, hc]
        exact hw
      have hcw : iT c = (w : V) := mul_left_cancel₀ hyT e
      have hc' : IsUnit c := (isUnit_map_iff iT c).mp (by rw [hcw]; exact w.isUnit)
      refine ⟨hc'.unit, ?_⟩
      rw [IsUnit.unit_spec, mul_comm, hc]
end GlobalTheory
