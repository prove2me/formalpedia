-- Prove2me | solution 1 for IsLocalRing.exists_jointly_injective_isLocalHom_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/89c7bbc4-466a-562d-93c7-b04fd2c1ea79

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_jointly_injective_isLocalHom_of_isReduced

set_option autoImplicit false

open IsLocalRing

theorem solution
    (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsReduced T] :
    ∃ (n : ℕ) (A : Fin n → Type) (_ : ∀ i, CommRing (A i)) (_ : ∀ i, IsDomain (A i))
      (_ : ∀ i, IsLocalRing (A i)) (_ : ∀ i, IsNoetherianRing (A i)) (χ : ∀ i, T →+* A i),
      (∀ i, IsLocalHom (χ i)) ∧ (∀ i, Function.Surjective (χ i)) ∧
        (∀ x : T, (∀ i, χ i x = 0) → x = 0) := by
  classical
  have hfin := minimalPrimes.finite_of_isNoetherianRing T
  set s := hfin.toFinset with hs
  let e := s.equivFin
  let 𝔭 : Fin s.card → Ideal T := fun i => (e.symm i).1
  have h𝔭 : ∀ i, 𝔭 i ∈ minimalPrimes T := fun i => hfin.mem_toFinset.mp (e.symm i).2
  have hprime : ∀ i, (𝔭 i).IsPrime := fun i => Ideal.minimalPrimes_isPrime (h𝔭 i)
  have hdom : ∀ i, IsDomain (T ⧸ 𝔭 i) := fun i => by
    haveI := hprime i
    infer_instance
  have hloc : ∀ i, IsLocalRing (T ⧸ 𝔭 i) := fun i => by
    haveI := hdom i
    exact IsLocalRing.of_surjective' (Ideal.Quotient.mk (𝔭 i)) Ideal.Quotient.mk_surjective
  refine ⟨s.card, fun i => T ⧸ 𝔭 i, inferInstance, hdom, hloc, fun i => inferInstance, fun i => Ideal.Quotient.mk (𝔭 i),
    fun i => ?_, fun i => Ideal.Quotient.mk_surjective, ?_⟩
  · haveI := hdom i
    haveI := hloc i
    exact IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  · intro x hx
    have hmem : x ∈ sInf (minimalPrimes T) := by
      rw [Ideal.mem_sInf]
      intro J hJ
      have hJs : J ∈ s := hfin.mem_toFinset.mpr hJ
      have hi : 𝔭 (e ⟨J, hJs⟩) = J := by
        show (e.symm (e ⟨J, hJs⟩)).1 = J
        rw [Equiv.symm_apply_apply]
      rw [← hi]
      exact Ideal.Quotient.eq_zero_iff_mem.mp (hx _)
    have hbot : sInf (minimalPrimes T) = ⊥ := by
      rw [minimalPrimes, Ideal.sInf_minimalPrimes]
      exact nilradical_eq_zero T
    rw [hbot] at hmem
    exact hmem

end S_IsLocalRing_exists_jointly_injective_isLocalHom_of_isReduced
end P2MW
export P2MW.S_IsLocalRing_exists_jointly_injective_isLocalHom_of_isReduced (solution)
