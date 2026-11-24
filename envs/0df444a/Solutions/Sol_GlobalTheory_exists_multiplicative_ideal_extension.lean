-- Prove2me | solution 1 for GlobalTheory.exists_multiplicative_ideal_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:44:46.571005+00:00
-- url     : https://prove2.me/submissions/8dbd05c0-41d5-4d7e-bd6e-b35ae5f7d5aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RayCharacterExtendsToIdeals

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
open UniqueFactorizationMonoid
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (c : HeightOneSpectrum (𝓞 K) → ℂ), (∀ P, ¬ m ≤ P.asIdeal → ‖c P‖ = 1) → ∃ X : Ideal (𝓞 K) → ℂ, X ⊥ = 0 ∧ X ⊤ = 1 ∧ (∀ I J, X (I * J) = X I * X J) ∧ (∀ I, I ≠ ⊥ → I ⊔ m = ⊤ → ‖X I‖ = 1) ∧ (∀ I, I ⊔ m ≠ ⊤ → X I = 0) ∧ ∀ P, ¬ m ≤ P.asIdeal → X P.asIdeal = c P := by
  intro K _ _ m c hc
  let d : Ideal (𝓞 K) → ℂ := fun Q =>
    if h : Q.IsPrime ∧ Q ≠ ⊥ then (if m ≤ Q then 0 else c ⟨Q, h.1, h.2⟩) else 0
  have hd : ∀ P : HeightOneSpectrum (𝓞 K), ¬ m ≤ P.asIdeal → d P.asIdeal = c P := by
    intro P hP
    simp only [d]
    rw [dif_pos ⟨P.isPrime, P.ne_bot⟩, if_neg hP]
  have hd0 : ∀ Q, m ≤ Q → d Q = 0 := by
    intro Q hQ
    simp only [d]
    split_ifs <;> rfl
  refine ⟨fun I => if I = ⊥ then 0 else ((normalizedFactors I).map d).prod, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · have : (⊤ : Ideal (𝓞 K)) ≠ ⊥ := top_ne_bot
    simp only [if_neg this]
    rw [← Ideal.one_eq_top, normalizedFactors_one]
    simp
  · intro I J
    by_cases hI : I = ⊥
    · simp [hI]
    by_cases hJ : J = ⊥
    · simp [hJ]
    have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
    simp only [if_neg hI, if_neg hJ, if_neg hIJ]
    rw [normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]
  · intro I hI hm
    simp only [if_neg hI]
    refine Multiset.prod_induction (fun z : ℂ => ‖z‖ = 1) _ ?_ (by simp) ?_
    · intro a b ha hb
      simp [ha, hb]
    · intro a ha
      obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.1 ha
      have hp : Prime Q := prime_of_normalized_factor Q hQ
      have hle : I ≤ Q := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hQ)
      have hQp : Q.IsPrime := Ideal.isPrime_of_prime hp
      have hm' : ¬ m ≤ Q := fun h => hQp.ne_top (top_le_iff.1 (hm ▸ sup_le hle h))
      have := hd ⟨Q, hQp, hp.ne_zero⟩ hm'
      simp only at this
      rw [this]
      exact hc _ hm'
  · intro I hm
    by_cases hI : I = ⊥
    · simp [hI]
    simp only [if_neg hI]
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hm
    apply Multiset.prod_eq_zero
    refine Multiset.mem_map.2 ⟨Q, ?_, hd0 Q (le_sup_right.trans hle)⟩
    exact (Ideal.mem_normalizedFactors_iff hI).2 ⟨hQ.isPrime, le_sup_left.trans hle⟩
  · intro P hP
    simp only [if_neg P.ne_bot]
    rw [normalizedFactors_irreducible P.irreducible, normalize_eq]
    simp [hd P hP]
end GlobalTheory
