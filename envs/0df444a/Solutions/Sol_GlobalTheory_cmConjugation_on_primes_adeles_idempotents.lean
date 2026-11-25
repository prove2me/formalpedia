-- Prove2me | solution 1 for GlobalTheory.cmConjugation_on_primes_adeles_idempotents
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:05:48.380826+00:00
-- url     : https://prove2.me/submissions/a36e5a9f-c034-4d2f-8fdf-29824f67221b

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_ThmBInHecke
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPrimeInvolutionOfRingInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CmConjugationOnPrimesProperties
import Theorems.Thm_GlobalTheory_conjIdem_sigR_sigR
import Theorems.Thm_GlobalTheory_conjIdem_sigR_algebraMap
import Theorems.Thm_GlobalTheory_conjIdem_sigR_inclR
import Theorems.Thm_GlobalTheory_conjIdem_finPart_cA
import Theorems.Thm_GlobalTheory_conjIdem_sigR_mem_intAE
import Theorems.Thm_GlobalTheory_cmConjugation_on_primes


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ c : HeightOneSpectrum (𝓞 E) ≃ HeightOneSpectrum (𝓞 E), (∀ P, c (c P) = P) ∧ (∀ P, normP (c P) = normP P) ∧ (∀ P (x y : 𝓞 E), (y : E) = σ x → (y ∈ (c P).asIdeal ↔ x ∈ P.asIdeal) ∧ (y ∈ (c P).asIdeal ^ 2 ↔ x ∈ P.asIdeal ^ 2)) ∧ (∀ P Q : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = Q.under (𝓞 F) ↔ Q = P ∨ Q = c P) ∧ (∀ y, cA σ (cA σ y) = y) ∧ (∀ y : AE F E, finPart F E (cA σ y) ∈ intAE F E ↔ finPart F E y ∈ intAE F E) ∧ ∀ P e f, IsPrimeIdem σ P e f → IsPrimeIdem σ (c P) (cA σ e) f := by
  intro F E _ _ _ _ _ σ hCM
  obtain ⟨h1, h2, h3, h4⟩ := hCM
  obtain ⟨hinv, c, hc1, hc2, hint, hc3, hc4⟩ := cmConjugation_on_primes F E σ h1 h2 h3 h4
  have hcc : ∀ y : AE F E, cA σ (cA σ y) = y := conjIdem_sigR_sigR (AF F) σ hinv
  have hfin : ∀ y : AE F E, finPart F E (cA σ y) ∈ intAE F E ↔ finPart F E y ∈ intAE F E := by
    have key : ∀ y : AE F E, finPart F E y ∈ intAE F E → finPart F E (cA σ y) ∈ intAE F E := by
      intro y hy
      rw [conjIdem_finPart_cA]
      exact conjIdem_sigR_mem_intAE σ hint _ hy
    intro y
    exact ⟨fun h => by have := key _ h; rwa [hcc] at this, key y⟩
  have hcrit : ∀ (P : HeightOneSpectrum (𝓞 E)) (e : AE F E),
      (∀ x : 𝓞 E, x ≠ 0 →
        (x ∈ P.asIdeal ↔ finPart F E (e * incA F E ((x : E)⁻¹)) ∉ intAE F E)) →
      ∀ x : 𝓞 E, x ≠ 0 →
        (x ∈ (c P).asIdeal ↔ finPart F E (cA σ e * incA F E ((x : E)⁻¹)) ∉ intAE F E) := by
    intro P e h x hx
    obtain ⟨z, hz⟩ := hint x
    have hxz : (x : E) = σ z := by rw [hz, hinv]
    have hz0 : z ≠ 0 := by
      rintro rfl
      apply hx
      apply RingOfIntegers.ext
      rw [hxz]
      simp
    have hm : cA σ e * incA F E ((x : E)⁻¹) = cA σ (e * incA F E ((z : E)⁻¹)) := by
      rw [map_mul, conjIdem_sigR_inclR, map_inv₀ σ, hxz]
    rw [(hc3 P z x hxz).1, h z hz0, hm, hfin]
  refine ⟨c, hc1, hc2, hc3, hc4, hcc, hfin, ?_⟩
  intro P e f h
  rcases h with ⟨⟨⟨he1, he2, v, ε, hv, he3⟩, hP⟩, hf⟩ | ⟨hf, ⟨v, ε, hv, he⟩, hP⟩
  · left
    refine ⟨⟨⟨?_, ?_, v, ε, hv, ?_⟩, hcrit P e hP⟩, ?_⟩
    · rw [← map_mul, he1]
    · rw [hcc, mul_comm, he2]
    · rw [hcc, add_comm, he3]
    · rw [hcc, add_comm, hf]
  · right
    have hce : cA σ e = e := by rw [he]; exact conjIdem_sigR_algebraMap _ σ ε
    exact ⟨by rw [hce, hf], ⟨v, ε, hv, by rw [hce, he]⟩, hcrit P e hP⟩
end GlobalTheory
