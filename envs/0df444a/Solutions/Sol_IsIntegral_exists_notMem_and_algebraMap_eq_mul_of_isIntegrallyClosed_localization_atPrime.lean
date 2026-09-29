-- Prove2me | solution 1 for IsIntegral.exists_notMem_and_algebraMap_eq_mul_of_isIntegrallyClosed_localization_atPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/039735fb-eb33-5768-8a7b-339de2a7e758

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsIntegral_exists_notMem_and_algebraMap_eq_mul_of_isIntegrallyClosed_localization_atPrime

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution
    {B F : Type*} [CommRing B] [CommRing F] [Algebra B F]
    (M : Submonoid B) (hM : M ≤ nonZeroDivisors B) [IsLocalization M F]
    (𝔮 : Ideal B) [𝔮.IsPrime] [IsDomain (Localization.AtPrime 𝔮)] [IsIntegrallyClosed (Localization.AtPrime 𝔮)]
    (t : F) (ht : IsIntegral B t) :
    ∃ s : B, s ∉ 𝔮 ∧ ∃ c : B, algebraMap B F c = algebraMap B F s * t := by
  classical

  have hMne : ∀ m : M, algebraMap B (Localization.AtPrime 𝔮) (m : B) ≠ 0 := by
    intro m hm0
    obtain ⟨u, hu⟩ := (IsLocalization.map_eq_zero_iff 𝔮.primeCompl (Localization.AtPrime 𝔮) _).1 hm0
    have hu0 : (u : B) = 0 := (mem_nonZeroDivisors_iff_right.1 (hM m.2)) _ hu
    exact u.2 (by rw [hu0]; exact 𝔮.zero_mem)

  let L := FractionRing (Localization.AtPrime 𝔮)
  let g : B →+* L :=
    (algebraMap (Localization.AtPrime 𝔮) L).comp (algebraMap B (Localization.AtPrime 𝔮))
  have hgapp : ∀ x : B, g x = algebraMap (Localization.AtPrime 𝔮) L (algebraMap B (Localization.AtPrime 𝔮) x) :=
    fun x => rfl
  have hg : ∀ m : M, IsUnit (g m) := fun m =>
    isUnit_iff_ne_zero.2 fun h0 => hMne m
      ((IsFractionRing.injective (Localization.AtPrime 𝔮) L) (by rw [map_zero]; exact h0))
  let φ : F →+* L := IsLocalization.lift hg
  have hφ : ∀ x : B, φ (algebraMap B F x) = g x := IsLocalization.lift_eq hg

  have hint : IsIntegral (Localization.AtPrime 𝔮) (φ t) := by
    obtain ⟨p, hpm, hp0⟩ := ht
    refine ⟨p.map (algebraMap B (Localization.AtPrime 𝔮)), hpm.map _, ?_⟩
    have hcomp : (algebraMap (Localization.AtPrime 𝔮) L).comp (algebraMap B (Localization.AtPrime 𝔮)) =
        φ.comp (algebraMap B F) := by
      ext x
      exact (hφ x).symm
    rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hp0, map_zero]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl y
  dsimp only at hy
  have hzero : φ (algebraMap B F (s : B) * t - algebraMap B F c) = 0 := by
    rw [map_sub, map_mul, hφ, hφ, ← hy, hgapp, hgapp, ← map_mul, IsLocalization.mk'_spec', sub_self]

  obtain ⟨⟨x, m⟩, hxm⟩ := IsLocalization.mk'_surjective M (algebraMap B F (s : B) * t - algebraMap B F c)
  dsimp only at hxm
  have hgx : g x = 0 := by
    have h1 : φ (IsLocalization.mk' F x m) = 0 := by rw [hxm]; exact hzero
    have h2 : φ (IsLocalization.mk' F x m) * g (m : B) = g x := by
      rw [← hφ, ← hφ, ← map_mul, IsLocalization.mk'_spec]
    rw [← h2, h1, zero_mul]
  have hx0 : algebraMap B (Localization.AtPrime 𝔮) x = 0 :=
    (IsFractionRing.injective (Localization.AtPrime 𝔮) L) (by rw [map_zero]; exact hgx)
  obtain ⟨s', hs'⟩ := (IsLocalization.map_eq_zero_iff 𝔮.primeCompl (Localization.AtPrime 𝔮) x).1 hx0
  have h3 : algebraMap B F (s' : B) * (algebraMap B F (s : B) * t - algebraMap B F c) = 0 := by
    rw [← hxm, IsLocalization.mul_mk'_eq_mk'_of_mul, hs', IsLocalization.mk'_zero]
  refine ⟨(s' : B) * s, fun hmem => ((inferInstance : 𝔮.IsPrime).mem_or_mem hmem).elim s'.2 s.2,
    (s' : B) * c, ?_⟩
  rw [map_mul, map_mul]
  linear_combination (-1 : F) * h3

end S_IsIntegral_exists_notMem_and_algebraMap_eq_mul_of_isIntegrallyClosed_localization_atPrime
end P2MW
export P2MW.S_IsIntegral_exists_notMem_and_algebraMap_eq_mul_of_isIntegrallyClosed_localization_atPrime (solution)
