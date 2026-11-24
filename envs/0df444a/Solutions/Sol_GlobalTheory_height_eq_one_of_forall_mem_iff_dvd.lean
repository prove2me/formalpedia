-- Prove2me | solution 1 for GlobalTheory.height_eq_one_of_forall_mem_iff_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:58:23.92643+00:00
-- url     : https://prove2.me/submissions/9bd196f8-2037-41c0-ae57-d20c1dc06099

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
open GlobalTheory
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
variable [IsIntegrallyClosed A]
namespace GlobalTheory
theorem _root_.solution {p : Ideal A} [hp : p.IsPrime] {a b : A} (ha : a ≠ 0)
    (h : ∀ r, r ∈ p ↔ a ∣ r * b) : p.height = 1 := by
  have hap : a ∈ p := (h a).mpr (dvd_mul_right a b)
  let K := FractionRing A
  have ha' : algebraMap A K a ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr ha
  obtain ⟨y, hy, k, hk, hyk⟩ : ∃ y ∈ p, ∃ k, k ∉ p ∧ y * b = a * k := by
    by_contra! H
    have hint := isIntegral_of_smul_mem_submodule (A := K)
      (Submodule.map (Algebra.linearMap A K) p) ?_ ?_ (algebraMap A K b / algebraMap A K a) ?_
    · obtain ⟨y, e⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
      refine hp.ne_top ((Ideal.eq_top_iff_one p).mpr ((h 1).mpr ⟨y, ?_⟩))
      apply IsFractionRing.injective A K
      rw [one_mul, map_mul, e, mul_div_cancel₀ _ ha']
    · rw [Submodule.ne_bot_iff]
      exact ⟨_, ⟨a, hap, rfl⟩, ha'⟩
    · exact Submodule.FG.map _ (IsNoetherian.noetherian _)
    · rintro _ ⟨m, hm, rfl⟩
      obtain ⟨k, hk⟩ := (h m).mp hm
      refine ⟨k, by_contra fun hkp => H m hm k hkp hk, ?_⟩
      change algebraMap A K k = algebraMap A K b / algebraMap A K a * algebraMap A K m
      rw [div_mul_eq_mul_div, ← map_mul, mul_comm b, hk, map_mul, mul_div_cancel_left₀ _ ha']
  have hmin : p ∈ (Ideal.span {y}).minimalPrimes := by
    refine ⟨⟨hp, (Ideal.span_singleton_le_iff_mem p).mpr hy⟩, ?_⟩
    rintro q ⟨hq, hyq⟩ hqp m hm
    obtain ⟨k', hk'⟩ := (h m).mp hm
    have e : k * m = y * k' := by
      apply mul_left_cancel₀ ha
      linear_combination y * hk' - m * hyk
    have : k * m ∈ q := e ▸ q.mul_mem_right _ ((Ideal.span_singleton_le_iff_mem q).mp hyq)
    exact (hq.mem_or_mem this).resolve_left fun hkq => hk (hqp hkq)
  refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hmin) ?_
  rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
  rintro rfl
  exact ha hap
end GlobalTheory
