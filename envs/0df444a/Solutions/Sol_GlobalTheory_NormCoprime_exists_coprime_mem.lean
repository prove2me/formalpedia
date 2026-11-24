-- Prove2me | solution 1 for GlobalTheory.NormCoprime.exists_coprime_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:29:26.400594+00:00
-- url     : https://prove2.me/submissions/5d4321a4-92c6-4ce4-9efe-c1df7c04fee8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoprimeIntegerInIdeal
import Theorems.Thm_GlobalTheory_NormCoprime_coprime_absNorm_of_sup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.NormCoprime
namespace GlobalTheory.NormCoprime
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (c : Ideal (𝓞 K)) (l : ℕ), l.Prime → c ≠ ⊥ →
    (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ c → (l : 𝓞 K) ∉ v.asIdeal) → ∃ m : ℕ, m.Coprime l ∧ (m : 𝓞 K) ∈ c := by
  intro K _ _ c l hl hc hv
  refine ⟨Ideal.absNorm c, ?_, Ideal.absNorm_mem c⟩
  refine coprime_absNorm_of_sup l hl hc ?_
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hlM : ((l : ℕ) : 𝓞 K) ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hcM : c ≤ M := le_trans le_sup_left hle
  have hM0 : M ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hlM
    exact hl.ne_zero (by exact_mod_cast hlM)
  exact hv ⟨M, hM.isPrime, hM0⟩ (Ideal.dvd_iff_le.mpr hcM) hlM
end GlobalTheory.NormCoprime
