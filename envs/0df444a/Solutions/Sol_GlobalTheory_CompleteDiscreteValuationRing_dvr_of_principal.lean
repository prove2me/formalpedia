-- Prove2me | solution 1 for GlobalTheory.CompleteDiscreteValuationRing.dvr_of_principal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:56:08.634791+00:00
-- url     : https://prove2.me/submissions/b8873334-b1cd-4856-bd06-4240a5ebe187

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDvrOfDimOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CompleteDiscreteValuationRing
namespace GlobalTheory.CompleteDiscreteValuationRing
theorem _root_.solution (S : Type) [CommRing S] [IsLocalRing S] (p : S)
    (hp : maximalIdeal S = Ideal.span {p}) (hreg : p ∈ nonZeroDivisors S)
    [IsHausdorff (maximalIdeal S) S] :
    ∃ _ : IsDomain S, IsDiscreteValuationRing S := by
  classical
  have hfac : ∀ x : S, x ≠ 0 → ∃ (n : ℕ) (u : S), IsUnit u ∧ x = p ^ n * u := by
    intro x hx
    have hex : ∃ n : ℕ, ¬ p ^ n ∣ x := by
      by_contra h
      push Not at h
      apply hx
      refine IsHausdorff.haus (I := maximalIdeal S) inferInstance x fun n => ?_
      rw [SModEq.zero, hp, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
      exact Ideal.mem_span_singleton.2 (h n)
    have h1 := Nat.find_spec hex
    have h0 : Nat.find hex ≠ 0 := fun h => by rw [h] at h1; simp at h1
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have h2 := Nat.find_min hex (m := n) (by omega)
    push Not at h2
    obtain ⟨u, hu⟩ := h2
    refine ⟨n, u, ?_, hu⟩
    by_contra hnu
    have : u ∈ maximalIdeal S := hnu
    rw [hp, Ideal.mem_span_singleton] at this
    apply h1
    rw [hn, hu, pow_succ]
    exact mul_dvd_mul_left _ this
  have hreg' : ∀ x : S, x ≠ 0 → x ∈ nonZeroDivisors S := by
    intro x hx
    obtain ⟨n, u, hu, rfl⟩ := hfac x hx
    exact mul_mem (pow_mem hreg n) hu.mem_nonZeroDivisors
  have hnz : NoZeroDivisors S := ⟨fun {x y} h => by
    by_cases hx : x = 0
    · exact Or.inl hx
    · exact Or.inr ((hreg' x hx).1 y h)⟩
  have hdom : IsDomain S := NoZeroDivisors.to_isDomain S
  have hp0 : p ≠ 0 := nonZeroDivisors.ne_zero hreg
  have hprime : Prime p := by
    rw [← Ideal.span_singleton_prime hp0, ← hp]
    infer_instance
  refine ⟨hdom, IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨p, hprime.irreducible, fun {x} hx => ?_⟩⟩
  obtain ⟨n, u, hu, rfl⟩ := hfac x hx
  exact ⟨n, hu.unit, rfl⟩
end GlobalTheory.CompleteDiscreteValuationRing
