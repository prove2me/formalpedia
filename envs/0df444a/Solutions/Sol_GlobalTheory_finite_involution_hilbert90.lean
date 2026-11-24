-- Prove2me | solution 1 for GlobalTheory.finite_involution_hilbert90
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:49:04.527867+00:00
-- url     : https://prove2.me/submissions/0ece5cbc-43d6-421e-9529-de81df85731a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FiniteInvolutionFixedUnitEqMulConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory
private lemma exists_pos_pow_mul_pow_eq_pow_of_finite {S : Type} [Monoid S] [Finite S] (a : S) :
    ∃ M : ℕ, 0 < M ∧ a ^ M * a ^ M = a ^ M := by
  have key : ∀ i j : ℕ, i < j → a ^ i = a ^ j → ∃ M : ℕ, 0 < M ∧ a ^ M * a ^ M = a ^ M := by
    intro i j hij h
    obtain ⟨p, rfl⟩ : ∃ p, j = i + (p + 1) := ⟨j - i - 1, by omega⟩
    have step : ∀ n, a ^ (i + n + (p + 1)) = a ^ (i + n) := by
      intro n
      rw [show i + n + (p + 1) = n + (i + (p + 1)) by ring, pow_add, ← h, ← pow_add,
        show n + i = i + n by ring]
    have rep : ∀ k n, a ^ (i + n + k * (p + 1)) = a ^ (i + n) := by
      intro k
      induction k with
      | zero => intro n; simp
      | succ k ih =>
        intro n
        rw [show i + n + (k + 1) * (p + 1) = i + (n + k * (p + 1)) + (p + 1) by ring, step,
          ← add_assoc, ih]
    refine ⟨(i + 1) * (p + 1), by positivity, ?_⟩
    rw [← pow_add]
    have hr := rep (i + 1) (i * p + p + 1)
    rwa [show i + (i * p + p + 1) + (i + 1) * (p + 1) = (i + 1) * (p + 1) + (i + 1) * (p + 1) by ring,
      show i + (i * p + p + 1) = (i + 1) * (p + 1) by ring] at hr
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => a ^ n)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i j hlt h
  · exact key j i hlt h.symm
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S : Type} [CommRing S] [Finite S] (c : S →+* S)
    (hc : ∀ x, c (c x) = x) (ω : S) (hω : IsUnit (ω - c ω)) (y : S) (hy : y * c y = 1) :
    ∃ x : S, IsUnit x ∧ x = y * c x := by
  have hyu : IsUnit y := ⟨⟨y, c y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩
  obtain ⟨M, hM0, hM⟩ := exists_pos_pow_mul_pow_eq_pow_of_finite ((1 + y) * c (1 + y))
  obtain ⟨e, he⟩ : ∃ e, e = ((1 + y) * c (1 + y)) ^ M := ⟨_, rfl⟩
  rw [← he] at hM
  have hce : c e = e := by
    rw [he, map_pow, map_mul, hc, mul_comm]
  have h1 : y * c (1 + y) = 1 + y := by
    rw [map_add, map_one]; linear_combination hy
  refine ⟨e * (1 + y) + (1 - e) * (ω + y * c ω), ?_, ?_⟩
  · by_contra hx
    obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hx)
    have hp := hm.isPrime
    have hnot : y * (ω - c ω) ∉ m := fun h => hm.ne_top (Ideal.eq_top_of_isUnit_mem m h (hyu.mul hω))
    have hid : ω * (1 + y) - (ω + y * c ω) = y * (ω - c ω) := by ring
    have hex : e ∈ m → 1 + y ∈ m := by
      intro h
      rw [he] at h
      rcases hp.mem_or_mem (hp.mem_of_pow_mem M h) with h' | h'
      · exact h'
      · rw [← h1]; exact m.mul_mem_left y h'
    by_cases hem : e ∈ m
    · have hx1 : 1 + y ∈ m := hex hem
      have h2 : (1 - e) * (ω + y * c ω) ∈ m := by
        have hr : (1 - e) * (ω + y * c ω)
            = (e * (1 + y) + (1 - e) * (ω + y * c ω)) - e * (1 + y) := by ring
        rw [hr]; exact m.sub_mem hxm (m.mul_mem_right _ hem)
      have h1e : 1 - e ∉ m := by
        intro h
        apply hm.ne_top
        rw [Ideal.eq_top_iff_one]
        have hs := m.add_mem hem h
        rwa [add_sub_cancel] at hs
      have hxω : ω + y * c ω ∈ m := (hp.mem_or_mem h2).resolve_left h1e
      apply hnot
      rw [← hid]
      exact m.sub_mem (m.mul_mem_left ω hx1) hxω
    · have hee : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hM, sub_self]
      have h1e : 1 - e ∈ m := by
        refine (hp.mem_or_mem ?_).resolve_left hem
        rw [hee]; exact m.zero_mem
      have h2 : e * (1 + y) ∈ m := by
        have hr : e * (1 + y)
            = (e * (1 + y) + (1 - e) * (ω + y * c ω)) - (1 - e) * (ω + y * c ω) := by ring
        rw [hr]; exact m.sub_mem hxm (m.mul_mem_right _ h1e)
      have hx1 : 1 + y ∈ m := (hp.mem_or_mem h2).resolve_left hem
      apply hem
      rw [he]
      exact Ideal.pow_mem_of_mem m (m.mul_mem_right _ hx1) M hM0
  · simp only [map_add, map_mul, map_sub, map_one, hc, hce]
    linear_combination (-(e + (1 - e) * ω)) * hy
end GlobalTheory
