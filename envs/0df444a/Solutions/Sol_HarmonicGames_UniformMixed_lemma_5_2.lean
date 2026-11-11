-- Prove2me | solution 1 for HarmonicGames.UniformMixed.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T08:04:09.871202+00:00
-- url     : https://prove2.me/submissions/bde5f5ae-3d57-4300-b253-e9466cbc260a

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Games
import Definitions.Def_HarmonicGames_GenericPure_Games
import Theorems.Thm_HarmonicGames_UniformMixed_lemma_A_1
import Theorems.Thm_HarmonicGames_Decomposition_lemma_4_5

open HarmonicGames.Decomposition

section Aux

variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
  [∀ m, DecidableEq (E m)]

private lemma c1_sum_apply {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {κ : Type*} (s : Finset κ) (X : κ → C1 G) (p q : V) :
    (∑ k ∈ s, X k) p q = ∑ k ∈ s, X k p q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

private lemma Dop_apply (u : Games E) (p q : ∀ k, E k) :
    (Dop E u) p q = ∑ k, (if MComparable E k p q then (1 : ℝ) else 0) * (u k q - u k p) := by
  show (∑ k, Dm E k (u k)) p q = _
  rw [c1_sum_apply]
  rfl

private lemma Dop_update (u : Games E) (m : ι) (p : ∀ k, E k) (a : E m) :
    (Dop E u) p (Function.update p m a) =
      u m (Function.update p m a) - u m p := by
  rw [Dop_apply, Finset.sum_eq_single m]
  · by_cases h : Function.update p m a = p
    · rw [h]; simp
    · have hc : MComparable E m p (Function.update p m a) := by
        refine ⟨fun e => h e.symm, fun k hk => ?_⟩
        simp [Function.update_of_ne hk]
      rw [if_pos hc, one_mul]
  · intro k _ hk
    have : ¬ MComparable E k p (Function.update p m a) := by
      rintro ⟨h1, h2⟩
      have hpm : p m = a := by
        have := h2 m (fun e => hk e.symm)
        simpa using this
      have e : Function.update p m a = p := by
        rw [← hpm]; exact Function.update_eq_self m p
      exact h1 e.symm
    simp [this]
  · intro h; exact absurd (Finset.mem_univ m) h

private lemma Dop_zero_of (u : Games E) (m : ι) (p q : ∀ k, E k) (h1 : p m ≠ q m)
    (h2 : ¬ ∀ j, j ≠ m → p j = q j) : (Dop E u) p q = 0 := by
  rw [Dop_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have : ¬ MComparable E k p q := by
    rintro ⟨_, h⟩
    by_cases hk : k = m
    · subst hk; exact h2 h
    · exact h1 (h m (fun e => hk e.symm))
  simp [this]

end Aux

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
    [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u : HarmonicGames.Decomposition.Games E) (hu : u ∈ HarmonicGames.GenericPure.harmonicGames E) (m : ι) (q r : E m) :
    ∑ p ∈ Finset.univ.filter (fun p : ∀ k, E k => p m = r),
      (HarmonicGames.GenericPure.payoff E u m p - HarmonicGames.GenericPure.payoff E u m (Function.update p m q)) = 0 := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : E m → Finset (∀ k, E k),
      ∀ r, S r = Finset.univ.filter (fun p : ∀ k, E k => p m = r) := ⟨_, fun _ => rfl⟩
  have hmem : ∀ r p, p ∈ S r ↔ p m = r := fun r p => by rw [hS]; simp
  rw [← hS]
  unfold HarmonicGames.GenericPure.payoff
  -- part N : nonstrategic games
  have hN : ∀ n ∈ nonstrategicSubspace E,
      ∑ p ∈ S r, (n m p - n m (Function.update p m q)) = 0 := by
    intro n hn
    refine Finset.sum_eq_zero fun p _ => ?_
    have h0 : (Dop E n) p (Function.update p m q) = 0 := by
      have : Dop E n = 0 := LinearMap.mem_ker.1 hn
      rw [this]; simp
    rw [Dop_update] at h0
    linarith
  -- part H : sums of a harmonic game over a slice vanish
  have hH0 : ∀ h ∈ harmonicSubspace E, ∀ r : E m, ∑ p ∈ S r, h m p = 0 := by
    intro h hh r
    have hPi : PiOp E h = h := by
      have := hh.1
      simpa [LinearMap.mem_eqLocus] using this.symm
    have hnormal : IsNormalized E h := ((lemma_4_5 ι E h).out 2 0).1 hPi
    have hdiv : LinearMap.adjoint (delta0 (gameGraph E)) (Dop E h) = 0 :=
      LinearMap.mem_ker.1 (Submodule.mem_comap.1 hh.2)
    have hA := HarmonicGames.UniformMixed.lemma_A_1 E (Dop E h) (S r)
    rw [hdiv] at hA
    simp only [PiLp.zero_apply, Finset.sum_const_zero] at hA
    have hinner : ∀ p ∈ S r, ∑ q ∈ (S r)ᶜ, (Dop E h) p q =
        - (Fintype.card (E m) : ℝ) * h m p := by
      intro p hp
      have hpm : p m = r := (hmem r p).1 hp
      have hsub : ∑ q ∈ (S r)ᶜ, (Dop E h) p q =
          ∑ a ∈ Finset.univ.filter (· ≠ r), (Dop E h) p (Function.update p m a) := by
        symm
        rw [← Finset.sum_image (f := fun q => (Dop E h) p q)
          (s := Finset.univ.filter (· ≠ r)) (g := fun a => Function.update p m a)
          (fun a _ b _ hab => by simpa using congrFun hab m)]
        apply Finset.sum_subset
        · intro q hq
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hq
          obtain ⟨a, ha, rfl⟩ := hq
          rw [Finset.mem_compl, hmem]
          simpa using ha
        · intro q hq hnq
          rw [Finset.mem_compl, hmem] at hq
          apply Dop_zero_of E h m p q (by rw [hpm]; exact fun e => hq e.symm)
          intro hall
          apply hnq
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨q m, hq, ?_⟩
          funext j
          by_cases hj : j = m
          · subst hj; simp
          · rw [Function.update_of_ne hj]; exact hall j hj
      rw [hsub]
      simp_rw [Dop_update]
      rw [Finset.filter_ne', Finset.sum_erase_eq_sub (Finset.mem_univ r)]
      have hr : Function.update p m r = p := by
        rw [← hpm]; exact Function.update_eq_self m p
      rw [hr, Finset.sum_sub_distrib, hnormal m p]
      simp
    have hsum : ∑ p ∈ S r, ∑ q ∈ (S r)ᶜ, (Dop E h) p q = 0 := by linarith
    rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum] at hsum
    have hc : (Fintype.card (E m) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := E m)).ne'
    have : ∑ p ∈ S r, h m p = 0 := by
      have h2 : (-(Fintype.card (E m) : ℝ)) * ∑ p ∈ S r, h m p = 0 := by
        simpa [Finset.sum_mul, neg_mul] using hsum
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact absurd (neg_eq_zero.1 h3) hc
      · exact h3
    exact this
  have hH : ∀ h ∈ harmonicSubspace E,
      ∑ p ∈ S r, (h m p - h m (Function.update p m q)) = 0 := by
    intro h hh
    rw [Finset.sum_sub_distrib, hH0 h hh r, zero_sub, neg_eq_zero]
    have hbij : ∑ p ∈ S r, h m (Function.update p m q) = ∑ p ∈ S q, h m p := by
      refine Finset.sum_nbij' (fun p => Function.update p m q) (fun p => Function.update p m r)
        ?_ ?_ ?_ ?_ ?_
      · intro p _; rw [hmem]; simp
      · intro p _; rw [hmem]; simp
      · intro p hp
        have hpm : p m = r := (hmem r p).1 hp
        simp only [Function.update_idem]
        rw [← hpm]; exact Function.update_eq_self m p
      · intro p hp
        have hpm : p m = q := (hmem q p).1 hp
        simp only [Function.update_idem]
        rw [← hpm]; exact Function.update_eq_self m p
      · intro p _; rfl
    rw [hbij, hH0 h hh q]
  obtain ⟨h, hh, n, hn, rfl⟩ := Submodule.mem_sup.1 hu
  have := hH h hh
  have := hN n hn
  simp only [PiLp.add_apply, Finset.sum_sub_distrib] at *
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  linarith
