-- Prove2me | solution 1 for MarkovMixing.period_eq_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T03:19:48.944861+00:00
-- url     : https://prove2.me/submissions/7fa6b26e-4bf4-465e-8e37-2585ed7a9fd8

import Definitions.Def_mm_basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Order.ConditionallyCompleteLattice.Finset

open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P) (x y : V) :
    period P x = period P y := by
  classical
  -- entries of every power are nonnegative
  have hpow_nonneg : ∀ (t : ℕ) (a b : V), 0 ≤ (P ^ t) a b := by
    intro t
    induction t with
    | zero => intro a b; by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    | succ n ih =>
        intro a b
        rw [pow_succ]
        exact Finset.sum_nonneg fun z _ => mul_nonneg (ih a z) (hP.1 z b)
  -- Chapman–Kolmogorov lower bound through an intermediate state
  have hchain : ∀ (a b : ℕ) (u v w : V),
      (P ^ a) u v * (P ^ b) v w ≤ (P ^ (a + b)) u w := by
    intro a b u v w
    have hsum : (P ^ (a + b)) u w = ∑ z, (P ^ a) u z * (P ^ b) z w := by
      rw [pow_add]; rfl
    rw [hsum]
    refine Finset.single_le_sum (f := fun z => (P ^ a) u z * (P ^ b) z w)
      (fun z _ => mul_nonneg (hpow_nonneg a u z) (hpow_nonneg b z w)) (Finset.mem_univ v)
  -- the return set of any state is nonempty
  have hret_ne : ∀ a : V, (returnSet P a).Nonempty := by
    intro a
    obtain ⟨b, -, hb⟩ : ∃ b ∈ (Finset.univ : Finset V), 0 < P a b := by
      by_contra hcon
      push_neg at hcon
      have : ∑ b, P a b ≤ 0 :=
        Finset.sum_nonpos fun b hb => hcon b hb
      rw [hP.2 a] at this
      linarith
    obtain ⟨s, hs⟩ := hirr b a
    refine ⟨1 + s, ⟨by omega, ?_⟩⟩
    have h1 : (P ^ 1) a b * (P ^ s) b a ≤ (P ^ (1 + s)) a a := hchain 1 s a b a
    have hpb : (0:ℝ) < (P ^ 1) a b := by simpa [pow_one] using hb
    nlinarith [mul_pos hpb hs]
  -- the divisor set is bounded above
  have hbdd : ∀ a : V, BddAbove {d : ℕ | ∀ t ∈ returnSet P a, d ∣ t} := by
    intro a
    obtain ⟨t₀, ht₀⟩ := hret_ne a
    refine ⟨t₀, fun d hd => Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one ht₀.1) (hd t₀ ht₀)⟩
    
  have hdiv_ne : ∀ a : V, {d : ℕ | ∀ t ∈ returnSet P a, d ∣ t}.Nonempty :=
    fun a => ⟨1, fun t _ => one_dvd t⟩
  -- the period really is a common divisor of the return times
  have hperiod_mem : ∀ a : V, ∀ t ∈ returnSet P a, period P a ∣ t := by
    intro a
    have := Nat.sSup_mem (hdiv_ne a) (hbdd a)
    exact this
  -- the key one-directional comparison
  have hle : ∀ u v : V, period P u ≤ period P v := by
    intro u v
    rcases eq_or_ne u v with rfl | huv
    · exact le_refl _
    · obtain ⟨r, hr⟩ := hirr u v
      obtain ⟨s, hs⟩ := hirr v u
      have hr1 : 1 ≤ r := by
        rcases Nat.eq_zero_or_pos r with rfl | h
        · exfalso
          rw [pow_zero, Matrix.one_apply] at hr
          by_cases h' : u = v
          · exact huv h'
          · rw [if_neg h'] at hr; linarith
        · exact h
      have hs1 : 1 ≤ s := by
        rcases Nat.eq_zero_or_pos s with rfl | h
        · exfalso
          rw [pow_zero, Matrix.one_apply] at hs
          by_cases h' : v = u
          · exact huv h'.symm
          · rw [if_neg h'] at hs; linarith
        · exact h
      -- `r + s` is a return time for `u`
      have hrs : r + s ∈ returnSet P u := by
        refine ⟨by omega, ?_⟩
        have h1 := hchain r s u v u
        nlinarith [mul_pos hr hs]
      -- `period P u` divides every return time of `v`
      have hmem : period P u ∈ {d : ℕ | ∀ t ∈ returnSet P v, d ∣ t} := by
        intro t ht
        have hrts : r + t + s ∈ returnSet P u := by
          refine ⟨by omega, ?_⟩
          have h1 := hchain r t u v v
          have h2 := hchain (r + t) s u v u
          have hpos : (0:ℝ) < (P ^ (r + t)) u v := by nlinarith [mul_pos hr ht.2]
          nlinarith [mul_pos hpos hs]
        have d1 : period P u ∣ (r + s) := hperiod_mem u _ hrs
        have d2 : period P u ∣ (r + t + s) := hperiod_mem u _ hrts
        have d3 := Nat.dvd_sub d2 d1
        rwa [show r + t + s - (r + s) = t by omega] at d3
      exact le_csSup (hbdd v) hmem
  exact le_antisymm (hle x y) (hle y x)
