-- Prove2me | solution 1 for MarkovMixing.exists_pow_pos
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T03:27:47.960144+00:00
-- url     : https://prove2.me/submissions/765c0b4d-2656-464e-a35e-cd4745d26e79

import Definitions.Def_mm_basic
import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (hap : Aperiodic P) :
    ∃ r : ℕ, 0 < r ∧ ∀ x y : V, 0 < (P ^ r) x y := by
  classical
  have hpow_nonneg : ∀ (s : ℕ) (a b : V), 0 ≤ (P ^ s) a b := by
    intro s
    induction s with
    | zero => intro a b; by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    | succ n ih =>
        intro a b
        rw [pow_succ]
        exact Finset.sum_nonneg fun z _ => mul_nonneg (ih a z) (hP.1 z b)
  have hchain : ∀ (a b : ℕ) (u v w : V),
      (P ^ a) u v * (P ^ b) v w ≤ (P ^ (a + b)) u w := by
    intro a b u v w
    have hsum : (P ^ (a + b)) u w = ∑ z, (P ^ a) u z * (P ^ b) z w := by
      rw [pow_add]; rfl
    rw [hsum]
    exact Finset.single_le_sum (f := fun z => (P ^ a) u z * (P ^ b) z w)
      (fun z _ => mul_nonneg (hpow_nonneg a u z) (hpow_nonneg b z w)) (Finset.mem_univ v)
  -- return sets are nonempty and closed under addition
  have hret_ne : ∀ a : V, ∃ t₀, t₀ ∈ returnSet P a := by
    intro a
    obtain ⟨b, -, hb⟩ : ∃ b ∈ (Finset.univ : Finset V), 0 < P a b := by
      by_contra hcon
      push_neg at hcon
      have hle : ∑ b, P a b ≤ 0 := Finset.sum_nonpos fun b hb => hcon b hb
      rw [hP.2 a] at hle
      linarith
    obtain ⟨s, hs⟩ := hirr b a
    refine ⟨1 + s, ⟨by omega, ?_⟩⟩
    have h1 : (P ^ 1) a b * (P ^ s) b a ≤ (P ^ (1 + s)) a a := hchain 1 s a b a
    have hpb : (0:ℝ) < (P ^ 1) a b := by simpa [pow_one] using hb
    nlinarith [mul_pos hpb hs]
  have hret_add : ∀ (a : V) (s t : ℕ), s ∈ returnSet P a → t ∈ returnSet P a →
      s + t ∈ returnSet P a := by
    intro a s t hs ht
    have hs1 := hs.1
    have ht1 := ht.1
    refine ⟨by omega, ?_⟩
    have h1 := hchain s t a a a
    nlinarith [mul_pos hs.2 ht.2]
  -- aperiodicity says the gcd of the return set is one
  have hgcd : ∀ a : V, Nat.setGcd (returnSet P a) = 1 := by
    intro a
    obtain ⟨t₀, ht₀⟩ := hret_ne a
    have hg_dvd : Nat.setGcd (returnSet P a) ∣ t₀ := Nat.setGcd_dvd_of_mem ht₀
    have hgpos : 0 < Nat.setGcd (returnSet P a) := by
      rcases Nat.eq_zero_or_pos (Nat.setGcd (returnSet P a)) with h | h
      · rw [h] at hg_dvd
        have h0 := Nat.eq_zero_of_zero_dvd hg_dvd
        have h1 := ht₀.1
        omega
      · exact h
    have hset : {d : ℕ | ∀ t ∈ returnSet P a, d ∣ t}
        = {d : ℕ | d ∣ Nat.setGcd (returnSet P a)} := by
      ext d
      simp only [Set.mem_setOf_eq]
      exact Nat.dvd_setGcd_iff.symm
    have hsup : sSup {d : ℕ | ∀ t ∈ returnSet P a, d ∣ t} = Nat.setGcd (returnSet P a) := by
      rw [hset]
      have hne : ({d : ℕ | d ∣ Nat.setGcd (returnSet P a)}).Nonempty :=
        ⟨Nat.setGcd (returnSet P a), dvd_rfl⟩
      have hbd : BddAbove {d : ℕ | d ∣ Nat.setGcd (returnSet P a)} :=
        ⟨Nat.setGcd (returnSet P a), fun d hd => Nat.le_of_dvd hgpos hd⟩
      refine le_antisymm (csSup_le hne fun d hd => Nat.le_of_dvd hgpos hd)
        (le_csSup hbd dvd_rfl)
    have := hap a
    rw [period, hsup] at this
    exact this
  -- every sufficiently large integer is a return time
  have hbig : ∀ a : V, ∃ N : ℕ, ∀ m : ℕ, N ≤ m → 1 ≤ m → m ∈ returnSet P a := by
    intro a
    obtain ⟨N, hN⟩ := Nat.exists_mem_closure_of_ge (s := returnSet P a)
    refine ⟨N, fun m hm hm1 => ?_⟩
    have hmem : m ∈ AddSubmonoid.closure (returnSet P a) := by
      refine hN m hm ?_
      rw [hgcd a]
      exact one_dvd m
    have hQ : ∀ k : ℕ, k ∈ AddSubmonoid.closure (returnSet P a) →
        k = 0 ∨ k ∈ returnSet P a := by
      intro k hk
      induction hk using AddSubmonoid.closure_induction with
      | mem z hz => exact Or.inr hz
      | zero => exact Or.inl rfl
      | add u v _ _ ihu ihv =>
          rcases ihu with rfl | hu
          · simpa using ihv
          · rcases ihv with rfl | hv
            · simpa using Or.inr hu
            · exact Or.inr (hret_add a u v hu hv)
    rcases hQ m hmem with h | h
    · omega
    · exact h
  choose N hN using hbig
  choose r hr using hirr
  refine ⟨(Finset.univ.sup N) + (Finset.univ.sup fun x => Finset.univ.sup fun y => r x y) + 1,
    by omega, ?_⟩
  intro x y
  set Nm := Finset.univ.sup N with hNm
  set Rm := Finset.univ.sup fun x => Finset.univ.sup fun y => r x y with hRm
  have hrle : r x y ≤ Rm := by
    refine le_trans ?_ (Finset.le_sup (f := fun x => Finset.univ.sup fun y => r x y)
      (Finset.mem_univ x))
    exact Finset.le_sup (f := fun y => r x y) (Finset.mem_univ y)
  have hNle : N x ≤ Nm := Finset.le_sup (Finset.mem_univ x)
  have hsplit : Nm + Rm + 1 = (Nm + Rm + 1 - r x y) + r x y := by omega
  have hmem : (Nm + Rm + 1 - r x y) ∈ returnSet P x :=
    hN x _ (by omega) (by omega)
  have hbound := hchain (Nm + Rm + 1 - r x y) (r x y) x x y
  rw [← hsplit] at hbound
  have := mul_pos hmem.2 (hr x y)
  linarith
