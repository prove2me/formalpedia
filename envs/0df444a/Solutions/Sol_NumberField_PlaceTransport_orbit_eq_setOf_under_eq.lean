-- Prove2me | solution 1 for NumberField.PlaceTransport.orbit_eq_setOf_under_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/60b9f238-a3cd-50ae-945b-cee1c9e2663d

import Mathlib
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceTransport_orbit_eq_setOf_under_eq

set_option autoImplicit false
open scoped NumberField.PlaceTransport
open scoped Pointwise

namespace P2mS26A2

open IsDedekindDomain NumberField

theorem numberField_of_algebra (E K : Type*) [Field E] [Field K] [NumberField K] [Algebra E K] : NumberField E := by
  haveI : CharZero E := RingHom.charZero (algebraMap E K)
  exact { to_charZero := inferInstance,
          to_finiteDimensional :=
            FiniteDimensional.of_injective (algebraMap E K).toRatAlgHom.toLinearMap (algebraMap E K).injective }

theorem smul_asIdeal_eq (E K : Type*) [Field E] [Field K] [Algebra E K] (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) :
    (σ • w).asIdeal = σ • w.asIdeal := by
  ext x
  rw [NumberField.PlaceTransport.mem_smul_asIdeal_iff, Ideal.mem_pointwise_smul_iff_inv_smul_mem]

end P2mS26A2

open IsDedekindDomain NumberField in
theorem solution (E K : Type*) [Field E] [Field K] [NumberField K]
    [Algebra E K] [IsGalois E K] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulAction.orbit (K ≃ₐ[E] K) w =
      {w' | w'.under (NumberField.RingOfIntegers E) = w.under (NumberField.RingOfIntegers E)} := by
  classical
  haveI : NumberField E := P2mS26A2.numberField_of_algebra E K
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : w.asIdeal.LiesOver (w.under (𝓞 E)).asIdeal := ⟨rfl⟩
  have horb := Algebra.IsInvariant.orbit_eq_primesOver (𝓞 E) (𝓞 K) (K ≃ₐ[E] K) (w.under (𝓞 E)).asIdeal w.asIdeal
  ext w'
  constructor
  · rintro ⟨σ, rfl⟩
    apply HeightOneSpectrum.ext
    change Ideal.under (𝓞 E) (σ • w).asIdeal = Ideal.under (𝓞 E) w.asIdeal
    rw [P2mS26A2.smul_asIdeal_eq, Ideal.under_smul]
  · intro hw'
    have hmem : w'.asIdeal ∈ (w.under (𝓞 E)).asIdeal.primesOver (𝓞 K) :=
      ⟨w'.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hw').symm⟩⟩
    rw [← horb] at hmem
    obtain ⟨σ, hσ⟩ := hmem
    refine ⟨σ, HeightOneSpectrum.ext ?_⟩
    change (σ • w).asIdeal = w'.asIdeal
    rw [P2mS26A2.smul_asIdeal_eq]
    exact hσ

end S_NumberField_PlaceTransport_orbit_eq_setOf_under_eq
end P2MW
export P2MW.S_NumberField_PlaceTransport_orbit_eq_setOf_under_eq (solution)
