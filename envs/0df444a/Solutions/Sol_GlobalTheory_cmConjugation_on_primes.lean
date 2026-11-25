-- Prove2me | solution 1 for GlobalTheory.cmConjugation_on_primes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:36:48.20614+00:00
-- url     : https://prove2.me/submissions/977179cd-06cb-42ef-8dc8-1b66a40604e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPrimeInvolutionOfRingInvolution
import Theorems.Thm_GlobalTheory_exists_primeInvolution_of_ringInvolution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) → (∀ x, σ (σ x) = x) ∧ ∃ c : HeightOneSpectrum (𝓞 E) ≃ HeightOneSpectrum (𝓞 E), (∀ P, c (c P) = P) ∧ (∀ P, Ideal.absNorm (c P).asIdeal = Ideal.absNorm P.asIdeal) ∧ (∀ x : 𝓞 E, ∃ y : 𝓞 E, (y : E) = σ x) ∧ (∀ P (x y : 𝓞 E), (y : E) = σ x → (y ∈ (c P).asIdeal ↔ x ∈ P.asIdeal) ∧ (y ∈ (c P).asIdeal ^ 2 ↔ x ∈ P.asIdeal ^ 2)) ∧ ∀ P Q : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = Q.under (𝓞 F) ↔ Q = P ∨ Q = c P := by
  intro F E _ _ _ _ _ σ _ hE h2 hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply τ.injective
    rw [hσ, hσ, star_star]
  have hfix : ∀ x, σ x = x → ∃ a : F, algebraMap F E a = x := by
    intro x hx
    have := Subalgebra.isSimpleOrder_of_finrank h2
    rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h | h
    · have hx' : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := hx
      rw [h] at hx'
      exact hx'
    · exfalso
      apply IsTotallyComplex.complexEmbedding_not_isReal τ
      rw [ComplexEmbedding.isReal_iff]
      ext y
      have hy : y ∈ AlgHom.equalizer σ (AlgHom.id F E) := by rw [h]; trivial
      have hy' : σ y = y := hy
      rw [ComplexEmbedding.conjugate_coe_eq]
      have := hσ τ y
      rw [hy'] at this
      exact this.symm
  let e : E ≃+* E :=
    { toFun := σ, invFun := σ, left_inv := hinv, right_inv := hinv,
      map_mul' := map_mul σ, map_add' := map_add σ }
  let s : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv e
  have hs : ∀ x : 𝓞 E, ((s x : 𝓞 E) : E) = σ x := fun x => rfl
  have hss : ∀ x, s (s x) = x := by
    intro x
    apply RingOfIntegers.ext
    rw [hs, hs, hinv]
  have hsF : ∀ a : 𝓞 F, s (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a := by
    intro a
    apply RingOfIntegers.ext
    rw [hs]
    exact σ.commutes (a : F)
  obtain ⟨c, hc1, hc2, hc3, hc4⟩ := exists_primeInvolution_of_ringInvolution s hss
  refine ⟨hinv, c, hc1, hc2, fun x => ⟨s x, hs x⟩, ?_, ?_⟩
  · intro P x y hy
    have : y = s x := RingOfIntegers.ext (by rw [hy, hs])
    subst this
    exact ⟨hc3 P x, hc4 P x⟩
  · intro P Q
    have hu : ∀ (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 F),
        a ∈ (P.under (𝓞 F)).asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) a ∈ P.asIdeal := fun P a => Iff.rfl
    constructor
    · intro h
      by_contra hne
      push Not at hne
      have hnot : ¬ ((Q.asIdeal : Set (𝓞 E)) ⊆ P.asIdeal ∪ (c P).asIdeal) := by
        rw [Ideal.subset_union]
        rintro (h' | h')
        · exact hne.1 (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h'))
        · exact hne.2 (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le (c P).isPrime.ne_top h'))
      rw [Set.not_subset] at hnot
      obtain ⟨x, hxQ, hx⟩ := hnot
      simp only [Set.mem_union, SetLike.mem_coe, not_or] at hx hxQ
      obtain ⟨a, ha⟩ := hfix ((x * s x : 𝓞 E) : E) (by
        rw [← hs, map_mul, hss, mul_comm])
      have hai : IsIntegral ℤ a := by
        have h1 : IsIntegral ℤ (algebraMap F E a) := by
          rw [ha]; exact RingOfIntegers.isIntegral_coe _
        exact (isIntegral_algebraMap_iff (algebraMap F E).injective).1 h1
      obtain ⟨b, hb⟩ : ∃ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b = x * s x :=
        ⟨⟨a, hai⟩, RingOfIntegers.ext ha⟩
      have h1 : b ∈ (Q.under (𝓞 F)).asIdeal := by
        rw [hu, hb]; exact Ideal.mul_mem_right _ _ hxQ
      rw [← h, hu, hb] at h1
      rcases P.isPrime.mem_or_mem h1 with h3 | h3
      · exact hx.1 h3
      · apply hx.2
        have := (hc3 P _).2 h3
        rwa [hss] at this
    · rintro (rfl | rfl)
      · rfl
      · ext a
        rw [hu, hu, ← hc3 P, hsF]
end GlobalTheory
