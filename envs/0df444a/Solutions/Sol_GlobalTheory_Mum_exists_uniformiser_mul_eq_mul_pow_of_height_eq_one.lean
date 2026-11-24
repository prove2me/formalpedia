-- Prove2me | solution 1 for GlobalTheory.Mum.exists_uniformiser_mul_eq_mul_pow_of_height_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:00:44.335976+00:00
-- url     : https://prove2.me/submissions/63808960-deda-4c8e-8293-230999ea364e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocalizationAtPrimeIsDiscreteValuationRingOfHeig
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulEqMulSqOfFaithfullyFlatHeightOne
import Theorems.Thm_GlobalTheory_localizationAtPrime_isDiscreteValuationRing_of_height_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.Mum
namespace GlobalTheory.Mum
theorem _root_.solution (O : Type) [CommRing O] [IsDomain O]
    [IsNoetherianRing O] [IsIntegrallyClosed O] (p : Ideal O) [hp : p.IsPrime] (h1 : p.height = 1)
    (h : O) (hh : h ≠ 0) :
    ∃ π ∈ p, π ≠ 0 ∧ (∀ y ∈ p, ∃ s ∉ p, π ∣ s * y) ∧
      ∃ (n : ℕ) (b c : O), b ∉ p ∧ c ∉ p ∧ b * h = c * π ^ n := by
  have := GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one O p h1
  let R := Localization.AtPrime p
  have hinj : Function.Injective (algebraMap O R) :=
    IsLocalization.injective R p.primeCompl_le_nonZeroDivisors
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨⟨π, s⟩, hs⟩ := IsLocalization.surj p.primeCompl ϖ
  have hsu : IsUnit (algebraMap O R s) := IsLocalization.map_units R s
  have hπ : Irreducible (algebraMap O R π) := by
    have e : algebraMap O R π = ϖ * algebraMap O R s := hs.symm
    rw [e]
    exact (irreducible_mul_isUnit hsu).2 hϖ
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπ
  refine ⟨π, ?_, ?_, ?_, ?_⟩
  · rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff R p π, hmax]
    exact Ideal.mem_span_singleton_self _
  · rintro rfl
    exact hπ.ne_zero (map_zero _)
  · intro y hy
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff R p y, hmax, Ideal.mem_span_singleton] at hy
    obtain ⟨z, hz⟩ := hy
    obtain ⟨⟨t, r⟩, hr⟩ := IsLocalization.surj p.primeCompl z
    refine ⟨r, r.2, t, hinj ?_⟩
    have hr' : z * algebraMap O R r = algebraMap O R t := hr
    rw [map_mul, map_mul, hz, ← hr']
    ring
  · have hh' : algebraMap O R h ≠ 0 := fun h0 => hh (hinj (by rw [h0, map_zero]))
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hh' hπ
    obtain ⟨⟨c, b⟩, hb⟩ := IsLocalization.surj p.primeCompl (u : R)
    have hb' : (u : R) * algebraMap O R b = algebraMap O R c := hb
    refine ⟨n, b, c, b.2, ?_, hinj ?_⟩
    · have hcu : IsUnit (algebraMap O R c) := by
        rw [← hb']
        exact u.isUnit.mul (IsLocalization.map_units R b)
      exact (IsLocalization.AtPrime.isUnit_to_map_iff R p c).1 hcu
    · rw [map_mul, map_mul, map_pow, hu, ← hb']
      ring
end GlobalTheory.Mum
