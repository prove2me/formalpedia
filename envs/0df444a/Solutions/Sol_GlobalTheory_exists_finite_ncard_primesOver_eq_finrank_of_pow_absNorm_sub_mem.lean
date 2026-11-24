-- Prove2me | solution 1 for GlobalTheory.exists_finite_ncard_primesOver_eq_finrank_of_pow_absNorm_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:31:23.942029+00:00
-- url     : https://prove2.me/submissions/e10e049b-acb0-45c7-a9bf-fd4f3dc25ae3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NcardPrimesOverEqFinrankOfTrivialFrobenius
import Theorems.Thm_GlobalTheory_natCard_le_of_forall_pow_eq_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
      [IsGalois K M], ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T →
        (∀ P ∈ v.asIdeal.primesOver (𝓞 M), ∀ x : 𝓞 M, x ^ Ideal.absNorm v.asIdeal - x ∈ P) →
        (v.asIdeal.primesOver (𝓞 M)).ncard = Module.finrank K M ∧
          ∀ P ∈ v.asIdeal.primesOver (𝓞 M), Ideal.absNorm P = Ideal.absNorm v.asIdeal := by
  intro K M _ _ _ _ _ _
  have hD : differentIdeal (𝓞 K) (𝓞 M) ≠ ⊥ := differentIdeal_ne_bot
  refine ⟨(fun P : HeightOneSpectrum (𝓞 M) => P.under (𝓞 K)) ''
    {P | P.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 M)}, (Ideal.finite_factors hD).image _, ?_⟩
  intro v hv hx
  haveI := v.isPrime
  have hq : 1 < Ideal.absNorm v.asIdeal := by
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    omega
  have hf : ∀ P ∈ v.asIdeal.primesOver (𝓞 M), P.inertiaDeg (𝓞 K) = 1 := by
    intro P hP
    haveI := hP.1
    haveI := hP.2
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
    haveI : Finite (𝓞 M ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
    have hle : Nat.card (𝓞 M ⧸ P) ≤ Ideal.absNorm v.asIdeal := by
      refine natCard_le_of_forall_pow_eq_self _ _ hq fun y => ?_
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← map_pow, Ideal.Quotient.eq]
      exact hx P hP x
    have hN : Ideal.absNorm P = Nat.card (𝓞 M ⧸ P) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have h := Ideal.absNorm_pow_inertiaDeg v.asIdeal P
    rw [← hN, ← h] at hle
    have hpos : 0 < P.inertiaDeg (𝓞 K) := P.inertiaDeg_pos (𝓞 K)
    have h2 : P.inertiaDeg (𝓞 K) ≤ 1 := by
      rw [← Nat.pow_le_pow_iff_right hq, pow_one]; exact hle
    omega
  have he : ∀ P ∈ v.asIdeal.primesOver (𝓞 M), P.ramificationIdx (𝓞 K) = 1 := by
    intro P hP
    haveI := hP.1
    haveI := hP.2
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
    have hn : ¬ P ∣ differentIdeal (𝓞 K) (𝓞 M) := by
      intro hd
      refine hv ⟨⟨P, hP.1, hP0⟩, hd, ?_⟩
      ext1
      exact (Ideal.over_def P v.asIdeal).symm
    haveI : Algebra.IsUnramifiedAt (𝓞 K) P := not_dvd_differentIdeal_iff.1 hn
    exact Ideal.ramificationIdx_eq_one P (𝓞 K)
  refine ⟨?_, fun P hP => ?_⟩
  · obtain ⟨P⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 M)))
    haveI := P.2.1
    haveI := P.2.2
    have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 M)
      Gal(M/K)
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P.1 Gal(M/K),
      Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal P.1 Gal(M/K), he P.1 P.2, hf P.1 P.2,
      IsGalois.card_aut_eq_finrank] at h
    simpa using h
  · haveI := hP.1
    haveI := hP.2
    rw [← Ideal.absNorm_pow_inertiaDeg v.asIdeal P, hf P hP, pow_one]
end GlobalTheory
