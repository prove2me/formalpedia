-- Prove2me | solution 1 for GlobalTheory.exists_pow_descent_cyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:45:45.577956+00:00
-- url     : https://prove2.me/submissions/dbe0bfc3-3977-40a2-a066-da1f1f204e8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowDescentCyclotomic
import Theorems.Thm_GlobalTheory_CyclotomicKummerDescent_geom_sum_valuation
import Theorems.Thm_GlobalTheory_CyclotomicKummerDescent_exists_aut
import Theorems.Thm_GlobalTheory_CyclotomicKummerDescent_descent

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
open CyclotomicKummerDescent
namespace GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] (l r : ℕ), l.Prime → ∃ M : ℕ, 0 < M ∧ l ^ r ∣ M ∧
    ∀ (Ω : Type) [Field Ω] [Algebra E Ω] (ζ : Ω), IsPrimitiveRoot ζ M → ∀ (u : E) (w : Ω),
      w ∈ IntermediateField.adjoin E {ζ} → w ^ M = algebraMap E Ω u →
        ∃ v : E, v ^ (l ^ r) = u := by
  intro E _ _ l r hl
  set m := (Module.finrank ℚ E).factorial with hm
  have ht1 : 1 < (1 + l ^ 2) ^ m :=
    Nat.one_lt_pow (Nat.factorial_ne_zero _) (by have := pow_pos hl.pos 2; omega)
  obtain ⟨k, hk⟩ : ∃ k, (1 + l ^ 2) ^ m = k + 1 := ⟨_, (Nat.sub_add_cancel ht1.le).symm⟩
  have hk0 : k ≠ 0 := by omega
  obtain ⟨s, e, he, hke⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk0 l hl.ne_one
  have hdiv : (l : ℤ) ^ 2 ∣ (((1 + l ^ 2) ^ m : ℕ) : ℤ) - 1 := by
    have := sub_dvd_pow_sub_pow (1 + (l : ℤ) ^ 2) 1 m
    simpa using this
  obtain ⟨hN1, hN2⟩ := geom_sum_valuation hl ht1 hdiv r
  rw [hk] at hN1 hN2
  refine ⟨l ^ (r + s), pow_pos hl.pos _, pow_dvd_pow _ (by omega), ?_⟩
  intro Ω _ _ ζ hζ u w hwK hw
  haveI : NeZero (l ^ (r + s)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hint : IsIntegral E ζ := (hζ.isIntegral (NeZero.pos _)).tower_top
  set K := IntermediateField.adjoin E {ζ} with hK
  haveI : IsCyclotomicExtension {l ^ (r + s)} E K := by
    change IsCyclotomicExtension {l ^ (r + s)} E K.toSubalgebra
    rw [hK, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hζ.adjoin_isCyclotomicExtension E
  let ζ' : K := ⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩
  have hζ' : IsPrimitiveRoot ζ' (l ^ (r + s)) :=
    IsPrimitiveRoot.of_map_of_injective (f := K.val) hζ K.val.injective
  let w' : K := ⟨w, hwK⟩
  have hw' : w' ^ (l ^ (r + s)) = algebraMap E K u := Subtype.ext hw
  rcases eq_or_ne u 0 with rfl | hu
  · exact ⟨0, zero_pow (pow_ne_zero _ hl.ne_zero)⟩
  have hw0 : w' ≠ 0 := by
    intro h
    rw [h, zero_pow (NeZero.ne _), eq_comm, map_eq_zero] at hw'
    exact hu hw'
  have hg : (1 + l ^ 2).Coprime (l ^ (r + s)) := by
    apply Nat.Coprime.pow_right
    rw [sq, Nat.coprime_add_mul_left_left]
    exact Nat.coprime_one_left l
  obtain ⟨τ, hτ⟩ := exists_aut (E := E) hζ' hg
  rw [← hm, hk] at hτ
  obtain ⟨α, v, hαM, hαN, hv⟩ := descent hζ' (n := l ^ r) τ hτ
    (by rw [pow_add]; exact mul_dvd_mul hN1 ⟨e, hke⟩) hw0 hw'
  have hαr : α ^ (l ^ r) = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hl).mp (orderOf_dvd_of_pow_eq_one hαM)
    have h1 := orderOf_dvd_of_pow_eq_one hαN
    rw [hj] at h1
    have hjr : j ≤ r := by
      by_contra hc
      exact hN2 ((pow_dvd_pow l (by omega)).trans h1)
    exact orderOf_dvd_iff_pow_eq_one.mp (hj ▸ pow_dvd_pow l hjr)
  have hvu : v ^ (l ^ r) = u ^ e := by
    apply (algebraMap E K).injective
    have h := congrArg (· ^ (l ^ r)) hv
    simp only [mul_pow, hαr, mul_one] at h
    rw [map_pow, map_pow, h, ← hw', hke, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hco : IsCoprime (e : ℤ) ((l ^ r : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr
      (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hl).mpr he).symm)
  obtain ⟨a, b, hab⟩ := hco
  refine ⟨v ^ a * u ^ b, ?_⟩
  rw [mul_pow, ← zpow_natCast (v ^ a), ← zpow_natCast (u ^ b), ← zpow_mul, ← zpow_mul, mul_comm a,
    zpow_mul, zpow_natCast, hvu, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hu, mul_comm _ a, hab,
    zpow_one]
end GlobalTheory
