-- Prove2me | solution 1 for GlobalTheory.phiEq_dvd_all_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:35:32.141798+00:00
-- url     : https://prove2.me/submissions/1dc8ac8d-bc2c-4a42-b872-c6d5d3b752d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FrobeniusPowEquationDvdAllPow
import Theorems.Thm_GlobalTheory_phiEq_iterate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u : R),
    ((l : ℕ) : R) = 0 → u ∈ nonZeroDivisors R → ∀ (κ : Type) [Fintype κ] (D : κ → R)
    (c : κ → κ → R) (h : ℕ), (∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) →
    (∀ j (M : ℕ), ∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * D j ^ n) → ∀ (m : ℕ) j, u ^ m ∣ D j := by
  intro l _ R _ u hl hu κ _ D c h hD hnil m j
  classical
  have hlp : l.Prime := Fact.out
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨0, Subsingleton.elim _ _⟩
  have hchar : ringChar R = l := by
    rcases (Nat.dvd_prime hlp).1 (ringChar.dvd hl) with h1 | h1
    · exact absurd h1 CharP.ringChar_ne_one
    · exact h1
  haveI : CharP R l := hchar ▸ ringChar.charP R
  haveI : ExpChar R l := ExpChar.prime hlp
  choose C hC using fun i => hnil i (h + 1)
  set Cm := ∑ i, C i with hCm
  obtain ⟨k, hk⟩ : ∃ k, m + Cm < l ^ k := ⟨m + Cm, Nat.lt_pow_self hlp.one_lt⟩
  obtain ⟨a, ha, e, he⟩ := phiEq_iterate l R u κ D c h hD k
  have hdiv : u ^ ((h + 1) * l ^ k) ∣ u ^ (Cm + a) * D j := by
    rw [pow_add, mul_assoc, he j, Finset.mul_sum]
    refine Finset.dvd_sum fun i _ => ?_
    rw [← mul_assoc]
    refine Dvd.dvd.mul_right ?_ _
    have hCi : C i ≤ Cm := Finset.single_le_sum (fun i _ => Nat.zero_le (C i)) (Finset.mem_univ i)
    refine (hC i (l ^ k)).trans ?_
    have hsp : u ^ Cm = u ^ C i * u ^ (Cm - C i) := by rw [← pow_add, Nat.add_sub_cancel' hCi]
    rw [hsp]
    exact ⟨u ^ (Cm - C i), by ring⟩
  have hle : Cm + a + m ≤ (h + 1) * l ^ k := by
    have : h * l ^ k + l ^ k = (h + 1) * l ^ k := by ring
    omega
  obtain ⟨y, hy⟩ := hdiv
  have hsplit : (h + 1) * l ^ k = (Cm + a) + ((h + 1) * l ^ k - (Cm + a)) := by omega
  rw [hsplit, pow_add u (Cm + a), mul_assoc] at hy
  have hreg : u ^ (Cm + a) ∈ nonZeroDivisors R := pow_mem hu _
  have hDj := (mul_cancel_left_mem_nonZeroDivisors hreg).1 hy
  rw [hDj]
  refine Dvd.dvd.mul_right (pow_dvd_pow u ?_) _
  omega
end GlobalTheory
