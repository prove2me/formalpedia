-- Prove2me | solution 1 for HorizontalPadicL.positiveDensityOrderlySet_to_primeSystem_inverseSeed_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T14:23:16.216225+00:00
-- url     : https://prove2.me/submissions/f07ba611-0aa4-44e3-9ef6-8aa5e42d91fd

import Definitions.Def_KN_InverseSeedConventionV2
import Theorems.Thm_HorizontalPadicL_positiveDensityPrimeSet_infinite_v2
import Definitions.Def_KN_SeededPrimeGaloisDataV2

set_option autoImplicit false
noncomputable section

open HorizontalPadicL

theorem solution
    {N k p m B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {f : MTT.Eigenform N k ι} {η : DirichletCharacterWithLevel}
    {V : SeededEigenformPadicPlaceData (p := p) f η}
    (hm : 0 < m)
    (D : SeededOrderlyFrobeniusClassData f η m B V)
    (δ : ℝ) (hδ : 0 < δ)
    (hdensity : HasPrimeNaturalDensity D.primes δ)
    (horderly : ∀ ⦃ℓ : ℕ⦄, ℓ ∈ D.primes →
      IsOrderlyPrimeForSeededEigenformV3 p m V.embedding f η ℓ) :
    ∃ L : SeededHorizontalPrimeSystemV3 p V.embedding f η B,
      L.orderExponent = m := by
  classical
  have hinfinite : D.primes.Infinite :=
    positiveDensityPrimeSet_infinite_v2 D.primes δ hδ hdensity
  letI : Infinite D.primes := Set.infinite_coe_iff.mpr hinfinite
  letI : Denumerable D.primes := Denumerable.ofEncodableOfInfinite D.primes
  let e : ℕ ≃ D.primes := (Denumerable.eqv D.primes).symm
  have hrange : {ℓ : ℕ | ∃ n : ℕ, (e n : ℕ) = ℓ} = D.primes := by
    ext ℓ
    constructor
    · rintro ⟨n, rfl⟩
      exact (e n).property
    · intro hℓ
      obtain ⟨n, hn⟩ := e.surjective ⟨ℓ, hℓ⟩
      exact ⟨n, congrArg Subtype.val hn⟩
  let L : SeededHorizontalPrimeSystemV3 p V.embedding f η B :=
    { orderExponent := m
      orderExponent_pos := hm
      primeAt := fun n => e n
      primeAt_prime := fun n => D.prime_of_mem (e n).property
      primeAt_injective := by
        intro a b hab
        apply e.injective
        exact Subtype.ext hab
      primeAt_avoids := fun n => D.avoids (e n).property
      primeAt_orderly := fun n => horderly (e n).property
      naturalDensity := δ
      naturalDensity_pos := hδ
      has_naturalDensity := by simpa [hrange] using hdensity }
  exact ⟨L, rfl⟩
