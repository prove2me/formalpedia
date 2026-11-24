-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.SplitPlace.split_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:21:42.965848+00:00
-- url     : https://prove2.me/submissions/fde698c2-55a7-4604-9ecd-b69136f48a97

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitsInCMFieldTwoPrimesDegreeOne
import Theorems.Thm_GlobalTheory_CMVal_Euler_SplitPlace_two_primes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler GlobalTheory.CMVal.Euler.SplitPlace
namespace GlobalTheory.CMVal.Euler.SplitPlace
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)), Splits v → (∀ P P' : HeightOneSpectrum (𝓞 E), Over P v → Over P' v → P ≠ P' → ∀ R : HeightOneSpectrum (𝓞 E), Over R v → R = P ∨ R = P') ∧ ∀ P : HeightOneSpectrum (𝓞 E), Over P v → Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ (∀ (a : OF E) (k : ℕ), algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal ^ k ↔ a ∈ v.asIdeal ^ k) ∧ ∀ b : 𝓞 E, ∃ a : OF E, b - algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal := by
  intro E _ _ _ v hv
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hmax : v.asIdeal.IsMaximal := v.isMaximal
  have hm : ∀ P : HeightOneSpectrum (𝓞 E), Over P v → P.asIdeal ∈ v.asIdeal.primesOver (𝓞 E) :=
    fun P h => ⟨P.isPrime, ⟨h.symm⟩⟩
  have hne : ∀ P P' (h : Over P v) (h' : Over P' v), P ≠ P' →
      (⟨_, hm P h⟩ : v.asIdeal.primesOver (𝓞 E)) ≠ ⟨_, hm P' h'⟩ :=
    fun P P' h h' hn he => hn (HeightOneSpectrum.ext (congrArg Subtype.val he))
  refine ⟨fun P P' h h' hn R hR => ?_, fun P hP => ?_⟩
  · rcases (two_primes _ E h2 v.asIdeal _ _ (hne P P' h h' hn)).1 ⟨_, hm R hR⟩ with e | e
    · exact Or.inl (HeightOneSpectrum.ext (congrArg Subtype.val e))
    · exact Or.inr (HeightOneSpectrum.ext (congrArg Subtype.val e))
  obtain ⟨Q, Q', hn, h, h'⟩ := hv
  have hef := (two_primes _ E h2 v.asIdeal _ _ (hne Q Q' h h' hn)).2 ⟨_, hm P hP⟩
  have hlo : P.asIdeal.LiesOver v.asIdeal := ⟨hP.symm⟩
  have hPm : P.asIdeal.IsMaximal := P.isMaximal
  have he : v.asIdeal.ramificationIdx' P.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]
    exact Nat.eq_one_of_mul_eq_one_right hef
  have hf : v.asIdeal.inertiaDeg' P.asIdeal = 1 := by
    rw [Ideal.inertiaDeg'_eq_inertiaDeg]
    exact Nat.eq_one_of_mul_eq_one_left hef
  refine ⟨?_, fun a k => ?_, fun b => ?_⟩
  · rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal v.asIdeal v.isPrime v.ne_bot, hf, pow_one]
  · rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.intValuation_le_pow_iff_mem,
      ← HeightOneSpectrum.intValuation_liesOver v P a, he, pow_one]
  · rw [Ideal.inertiaDeg'_algebraMap] at hf
    let _ := Ideal.Quotient.field v.asIdeal
    obtain ⟨c, hc⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 hf).2 (Ideal.Quotient.mk _ b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨a, Ideal.Quotient.eq.1 hc.symm⟩
end GlobalTheory.CMVal.Euler.SplitPlace
