-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GlobalFiniteness.natAbs_discr_mul_prod_absNorm_mem_of_dvd_differentIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:36:05.297808+00:00
-- url     : https://prove2.me/submissions/215fc9ec-b185-4501-8487-620272677348

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RamifiedPrimeContainsDiscriminant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GlobalFiniteness
namespace GlobalTheory.CompanionTheory.GlobalFiniteness
theorem _root_.solution
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal)
    (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hP0 : P ≠ ⊥) (hdvd : P ∣ differentIdeal ℤ (𝓞 E)) :
    (((discr F).natAbs * ∏ v ∈ S, v.asIdeal.absNorm : ℕ) : 𝓞 E) ∈ P := by
  by_contra ht
  have hv0 : P.under (𝓞 F) ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) hP0
  have hvp : (P.under (𝓞 F)).IsPrime := inferInstance
  let v : HeightOneSpectrum (𝓞 F) := ⟨P.under (𝓞 F), hvp, hv0⟩
  have hcast : ∀ (n : ℕ), (n : 𝓞 F) ∈ v.asIdeal → (n : 𝓞 E) ∈ P := fun n hn => by
    have : algebraMap (𝓞 F) (𝓞 E) (n : 𝓞 F) ∈ P := hn
    simpa [map_natCast] using this
  have hvS : v ∉ S := by
    intro hvS
    apply ht
    rw [Nat.cast_mul]
    apply Ideal.mul_mem_left
    have hd : v.asIdeal.absNorm ∣ ∏ w ∈ S, w.asIdeal.absNorm := Finset.dvd_prod_of_mem _ hvS
    obtain ⟨c, hc⟩ := hd
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hcast _ (Ideal.absNorm_mem _))
  have hlies : P.LiesOver v.asIdeal := ⟨rfl⟩
  have hun : Algebra.IsUnramifiedAt (𝓞 F) P := hS v hvS P hP hlies
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E)] at hdvd
  rcases (Ideal.prime_of_isPrime hP0 hP).dvd_or_dvd hdvd with h | h
  · exact not_dvd_differentIdeal_iff.2 hun h
  · apply ht
    rw [Nat.cast_mul]
    apply Ideal.mul_mem_right
    apply hcast
    have hmap : differentIdeal ℤ (𝓞 F) ≤ v.asIdeal := Ideal.map_le_iff_le_comap.1 (Ideal.le_of_dvd h)
    apply hmap
    rw [← absNorm_differentIdeal F (𝓞 F)]
    exact Ideal.absNorm_mem _
end GlobalTheory.CompanionTheory.GlobalFiniteness
