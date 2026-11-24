-- Prove2me | solution 1 for GlobalTheory.exists_isDomain_isDiscreteValuationRing_of_maximalIdeal_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:42:33.267944+00:00
-- url     : https://prove2.me/submissions/eae1fa53-7605-43fc-94f3-ab526202daaa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AssociatedPrimeLocalizationDvr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S : Type*} [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] {t : S} (ht : maximalIdeal S = Ideal.span {t})
    (hreg : IsSMulRegular S t) : ∃ _ : IsDomain S, IsDiscreteValuationRing S := by
  have hfac : ∀ y : S, y ≠ 0 → ∃ (n : ℕ) (u : S), IsUnit u ∧ y = t ^ n * u := by
    intro y hy
    have hinf : (⨅ i : ℕ, maximalIdeal S ^ i) = ⊥ :=
      Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top'
    have hex : ∃ n : ℕ, y ∉ maximalIdeal S ^ n := by
      by_contra! h
      exact hy (by simpa [hinf] using (Submodule.mem_iInf _).2 h)
    classical
    obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := by
      refine Nat.exists_eq_succ_of_ne_zero fun h0 ↦ ?_
      have := Nat.find_spec hex
      rw [h0] at this
      simp at this
    have h1 : y ∈ maximalIdeal S ^ k := by
      have := Nat.find_min hex (m := k) (by omega)
      simpa using this
    have h2 : y ∉ maximalIdeal S ^ (k + 1) := hk ▸ Nat.find_spec hex
    rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
    obtain ⟨u, rfl⟩ := h1
    refine ⟨k, u, ?_, rfl⟩
    by_contra hu
    apply h2
    have hum : u ∈ maximalIdeal S := (mem_maximalIdeal u).2 hu
    rw [ht, Ideal.mem_span_singleton] at hum
    obtain ⟨c, rfl⟩ := hum
    rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨c, by ring⟩
  have hnzd : NoZeroDivisors S := by
    refine ⟨fun {a b} hab ↦ ?_⟩
    by_contra hne
    push Not at hne
    obtain ⟨m, u, hu, rfl⟩ := hfac a hne.1
    obtain ⟨n, v, hv, rfl⟩ := hfac b hne.2
    have h0 : t ^ (m + n) • (u * v) = 0 := by
      rw [smul_eq_mul, pow_add]
      linear_combination hab
    have h3 : u * v = 0 := (hreg.pow (m + n)).right_eq_zero_of_smul h0
    exact (hu.mul hv).ne_zero h3
  have hdom : IsDomain S := NoZeroDivisors.to_isDomain S
  refine ⟨hdom, ?_⟩
  have ht0 : t ≠ 0 := fun h ↦ by
    have : IsSMulRegular S (0 : S) := h ▸ hreg
    exact one_ne_zero (this.right_eq_zero_of_smul (zero_smul S (1 : S)))
  have hf : ¬ IsField S := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ht]
    simpa using ht0
  refine ((IsDiscreteValuationRing.TFAE S hf).out 4 0).mp ?_
  exact ⟨t, ht⟩
end GlobalTheory
