-- Prove2me | solution 1 for GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:25:00.166177+00:00
-- url     : https://prove2.me/submissions/b0731365-0cfd-4112-9109-1bf510b1a11f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardPrimesOverEqFinrankOfAbsNormEqOfNotMemSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime →
      (∀ P : Ideal (𝓞 E), P.IsMaximal → ((p : 𝓞 E) ∈ P) →
        Ideal.absNorm P = p ∧ (p : 𝓞 E) ∉ P ^ 2) →
      (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  intro E _ _ p hp h
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  haveI hpr : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal := hpr.isMaximal hp0
  have hsum := Ideal.sum_ramification_inertia (𝓞 E) ℚ E (p := Ideal.span {(p : ℤ)}) hp0
  rw [← hsum, ← IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 E), Set.ncard_coe_finset,
    Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [IsDedekindDomain.mem_primesOverFinset_iff hp0] at hP
  obtain ⟨hPp, hPl⟩ := hP
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    simp [Ideal.map_span]
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact hPl.over.le
  have hmem : (p : 𝓞 E) ∈ P := by
    rw [hmap, Ideal.span_singleton_le_iff_mem] at hle
    exact hle
  have hPm : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {(p : ℤ)})
  obtain ⟨hN, hsq⟩ := h P hPm hmem
  have he : (Ideal.span {(p : ℤ)}).ramificationIdx' P = 1 := by
    by_contra hne
    have := (Ideal.ramificationIdx'_ne_one_iff hle).mp hne
    rw [hmap, Ideal.span_singleton_le_iff_mem] at this
    exact hsq this
  have hf : (Ideal.span {(p : ℤ)}).inertiaDeg' P = 1 := by
    have h1 := Ideal.absNorm_eq_pow_inertiaDeg' P hp
    rw [hN] at h1
    exact (Nat.pow_right_injective hp.two_le (by simpa using h1)).symm
  rw [he, hf]
end GlobalTheory
