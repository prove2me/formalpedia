-- Prove2me | solution 1 for GlobalTheory.adele_idem_prime_criterion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:34:01.829221+00:00
-- url     : https://prove2.me/submissions/afc66f17-63ad-420a-8d60-64efc9b0efbb

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_ThmBInHecke
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdeleIdemPrimeCriterion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors
namespace GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical in
open scoped TensorProduct ContDiff nonZeroDivisors in
private lemma one_lt_valued_inv_iff_mem {E : Type} [Field E] [NumberField E]
    (Q : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) (hx : x ≠ 0) :
    1 < Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (x : E)⁻¹) Q) ↔ x ∈ Q.asIdeal := by
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    map_inv₀, HeightOneSpectrum.valuation_of_algebraMap,
    ← HeightOneSpectrum.intValuation_lt_one_iff_mem]
  exact one_lt_inv₀ (zero_lt_iff.mpr (Q.intValuation_ne_zero x hx))
end GlobalTheory
end

set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors
open GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Φ : _root_.HeckeCharacterZeroLocus.ThmBIn.AE F E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E)), (∀ x : E, Φ (_root_.HeckeCharacterZeroLocus.ThmBIn.incA F E x) = (mixedEmbedding E x, algebraMap E _ x)) → (∀ y, _root_.HeckeCharacterZeroLocus.ThmBIn.finPart F E y ∈ _root_.HeckeCharacterZeroLocus.ThmBIn.intAE F E ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) → (∀ v ε, _root_.HeckeCharacterZeroLocus.ThmBIn.IsPlaceIdem F v ε → (Φ (algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε)).2 P = if P.under (𝓞 F) = v then 1 else 0) → ∀ (e : _root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) (ε : _root_.HeckeCharacterZeroLocus.ThmBIn.AF F), _root_.HeckeCharacterZeroLocus.ThmBIn.IsPlaceIdem F v ε → e * e = e → e * algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε = e → ((∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ _root_.HeckeCharacterZeroLocus.ThmBIn.finPart F E (e * _root_.HeckeCharacterZeroLocus.ThmBIn.incA F E ((x : E)⁻¹)) ∉ _root_.HeckeCharacterZeroLocus.ThmBIn.intAE F E)) ↔ ((Φ e).1 = 0 ∧ (Φ e).2 P = 1 ∧ ∀ Q, Q ≠ P → (Φ e).2 Q = 0)) := by
  intro F E _ _ _ _ _ Φ hΦ hint hplace e P v ε hε he heε
  obtain ⟨h0, -⟩ := hplace v ε hε
  have ha : (Φ e).1 = 0 := by
    have h := congrArg (fun z => (Φ z).1) heε
    simp only [map_mul, Prod.fst_mul, h0, mul_zero] at h
    exact h.symm
  have hidem : ∀ Q, (Φ e).2 Q = 0 ∨ (Φ e).2 Q = 1 := by
    intro Q
    have h := congrArg (fun z => (Φ z).2 Q) he
    rw [map_mul] at h
    exact IsIdempotentElem.iff_eq_zero_or_one.mp h
  have key : ∀ x : 𝓞 E, x ≠ 0 → (_root_.HeckeCharacterZeroLocus.ThmBIn.finPart F E (e * _root_.HeckeCharacterZeroLocus.ThmBIn.incA F E ((x : E)⁻¹)) ∉ _root_.HeckeCharacterZeroLocus.ThmBIn.intAE F E ↔
      ∃ Q, (Φ e).2 Q = 1 ∧ x ∈ Q.asIdeal) := by
    intro x hx
    rw [hint, map_mul, hΦ]
    push_neg
    constructor
    · rintro ⟨Q, hQ⟩
      change 1 < Valued.v ((Φ e).2 Q * (algebraMap E (FiniteAdeleRing (𝓞 E) E) (x : E)⁻¹) Q) at hQ
      rcases hidem Q with h | h
      · rw [h, zero_mul, map_zero] at hQ
        exact absurd hQ (not_lt.mpr zero_le')
      · rw [h, one_mul, one_lt_valued_inv_iff_mem Q x hx] at hQ
        exact ⟨Q, h, hQ⟩
    · rintro ⟨Q, h, hQ⟩
      refine ⟨Q, ?_⟩
      change 1 < Valued.v ((Φ e).2 Q * (algebraMap E (FiniteAdeleRing (𝓞 E) E) (x : E)⁻¹) Q)
      rw [h, one_mul, one_lt_valued_inv_iff_mem Q x hx]
      exact hQ
  constructor
  · intro hcrit
    have hS : ∀ Q, (Φ e).2 Q = 1 → Q = P := by
      intro Q hQ
      by_contra hne
      have hnle : ¬ Q.asIdeal ≤ P.asIdeal := fun hle =>
        hne (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top hle))
      obtain ⟨x, hxQ, hxP⟩ := Set.not_subset.mp hnle
      have hx : x ≠ 0 := fun h => hxP (h ▸ P.asIdeal.zero_mem)
      exact hxP ((hcrit x hx).mpr ((key x hx).mpr ⟨Q, hQ, hxQ⟩))
    obtain ⟨x, hxP, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    obtain ⟨Q, hQ, -⟩ := (key x hx).mp ((hcrit x hx).mp hxP)
    have hQP := hS Q hQ
    subst hQP
    refine ⟨ha, hQ, fun R hR => ?_⟩
    rcases hidem R with h | h
    · exact h
    · exact absurd (hS R h) hR
  · rintro ⟨-, hP, hQ⟩ x hx
    rw [key x hx]
    constructor
    · exact fun hxP => ⟨P, hP, hxP⟩
    · rintro ⟨Q, h, hxQ⟩
      by_cases hQP : Q = P
      · exact hQP ▸ hxQ
      · rw [hQ Q hQP] at h
        exact absurd h zero_ne_one
end _root_.GlobalTheory
end GlobalTheory
