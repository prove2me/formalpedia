-- Prove2me | solution 1 for GlobalTheory.CyclotomicKummerDescent.geom_sum_valuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:08:19.640943+00:00
-- url     : https://prove2.me/submissions/89b4c395-35f9-4df0-a7d4-b5d900e83f25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowDescentCyclotomic

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
open GlobalTheory.CyclotomicKummerDescent
namespace GlobalTheory.CyclotomicKummerDescent
theorem _root_.solution {l : ℕ} (hl : l.Prime) {t : ℕ} (ht1 : 1 < t)
    (ht : (l : ℤ) ^ 2 ∣ (t : ℤ) - 1) (r : ℕ) :
    l ^ r ∣ ∑ i ∈ Finset.range (l ^ r), t ^ i ∧
      ¬ l ^ (r + 1) ∣ ∑ i ∈ Finset.range (l ^ r), t ^ i := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have h1 : (l : ℤ) ∣ (t : ℤ) - 1 := (dvd_pow_self _ two_ne_zero).trans ht
  have h2 : ¬ (l : ℤ) ∣ (t : ℤ) := fun h => hp.not_dvd_one (by simpa using dvd_sub h h1)
  have hlte : emultiplicity (l : ℤ) ((t : ℤ) ^ (l ^ r) - 1 ^ (l ^ r)) =
      emultiplicity (l : ℤ) ((t : ℤ) - 1) + r := by
    rcases hl.eq_two_or_odd' with rfl | hodd
    · have h := Int.two_pow_sub_pow' (x := t) (y := 1) (2 ^ r) (by simpa using ht)
        (by simpa using h2)
      have h3 : emultiplicity (2 : ℤ) ((2 ^ r : ℕ) : ℤ) = r := by
        push_cast
        exact emultiplicity_pow_self_of_prime Int.prime_two r
      rw [h3] at h
      simpa using h
    · rw [Int.emultiplicity_pow_sub_pow hl hodd h1 h2,
        emultiplicity_pow_self_of_prime hl.prime]
  rw [one_pow, ← geom_sum_mul, emultiplicity_mul hp, add_comm] at hlte
  have hfin : emultiplicity (l : ℤ) ((t : ℤ) - 1) ≠ ⊤ := by
    rw [← finiteMultiplicity_iff_emultiplicity_ne_top, Int.finiteMultiplicity_iff]
    refine ⟨by simpa using hl.ne_one, ?_⟩
    have : (1 : ℤ) < t := by exact_mod_cast ht1
    omega
  have h4 : emultiplicity (l : ℤ) (∑ i ∈ Finset.range (l ^ r), (t : ℤ) ^ i) = (r : ℕ∞) :=
    WithTop.add_left_cancel hfin hlte
  rw [emultiplicity_eq_coe] at h4
  exact_mod_cast h4
end GlobalTheory.CyclotomicKummerDescent
