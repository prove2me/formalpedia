-- Prove2me | solution 1 for MLRPCake.EnvyFree.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:50:15.800825+00:00
-- url     : https://prove2.me/submissions/eaf3cdea-ec76-4e10-9ef2-5dbee634b10e

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Theorems.Thm_MLRPCake_EnvyFree_lemma_1

open MLRPCake.EnvyFree

namespace MLRPThm6Aux

lemma dens_eq {n : ℕ} (f : Fin n → ℝ → ℝ) (k : ℕ) (hk : k < n) : dens f k = f ⟨k, hk⟩ := by
  simp [dens, hk]

lemma val_eq {n : ℕ} (f : Fin n → ℝ → ℝ) (k : ℕ) (hk : k < n) (a b : ℝ) :
    val f k a b = ∫ t in a..b, f ⟨k, hk⟩ t := by
  simp [val, dens_eq f k hk]

/-- consecutive MLRP composes to MLRP for every ordered pair `p ≤ q`. -/
lemma ratio_mono {n : ℕ} (f : Fin n → ℝ → ℝ) (hmlrp : IsMLRP f) :
    ∀ d p q : ℕ, ∀ (hp : p < n) (hq : q < n), q = p + d → ∀ b c : ℝ, 0 ≤ b → b ≤ c → c ≤ 1 →
      f ⟨q, hq⟩ b / f ⟨p, hp⟩ b ≤ f ⟨q, hq⟩ c / f ⟨p, hp⟩ c := by
  intro d
  induction d with
  | zero =>
    intro p q hp hq hqp b c hb hbc hc
    have hq' : (⟨q, hq⟩ : Fin n) = ⟨p, hp⟩ := Fin.ext (by simp; omega)
    rw [hq']
    have h1 := hmlrp.1 ⟨p, hp⟩ b ⟨hb, by linarith⟩
    have h2 := hmlrp.1 ⟨p, hp⟩ c ⟨by linarith, hc⟩
    rw [div_self h1.ne', div_self h2.ne']
  | succ d ih =>
    intro p q hp hq hqp b c hb hbc hc
    have hr : p + d < n := by omega
    have hA := ih p (p + d) hp hr rfl b c hb hbc hc
    have hB := hmlrp.2 ⟨p + d, hr⟩ ⟨q, hq⟩ (by simp; omega) b c hb hbc hc
    have pb : ∀ k : Fin n, 0 < f k b := fun k => hmlrp.1 k b ⟨hb, by linarith⟩
    have pc : ∀ k : Fin n, 0 < f k c := fun k => hmlrp.1 k c ⟨by linarith, hc⟩
    have e1 : f ⟨q, hq⟩ b / f ⟨p, hp⟩ b =
        (f ⟨q, hq⟩ b / f ⟨p + d, hr⟩ b) * (f ⟨p + d, hr⟩ b / f ⟨p, hp⟩ b) := by
      field_simp [(pb ⟨p + d, hr⟩).ne', (pb ⟨p, hp⟩).ne']
    have e2 : f ⟨q, hq⟩ c / f ⟨p, hp⟩ c =
        (f ⟨q, hq⟩ c / f ⟨p + d, hr⟩ c) * (f ⟨p + d, hr⟩ c / f ⟨p, hp⟩ c) := by
      field_simp [(pc ⟨p + d, hr⟩).ne', (pc ⟨p, hp⟩).ne']
    rw [e1, e2]
    apply mul_le_mul hB hA
    · exact (div_pos (pb _) (pb _)).le
    · exact (div_pos (pc _) (pc _)).le

end MLRPThm6Aux

open MLRPThm6Aux

theorem solution (n : ℕ) (f : Fin n → ℝ → ℝ) (δ : ℝ) (x : ℕ → ℝ) (hf : IsInstance f)
    (hmlrp : IsMLRP f) (hδ : 0 ≤ δ) (hx : IsRipple f δ x) :
    ∀ i j : ℕ, i < n → j < n → val f i (x j) (x (j + 1)) ≤ val f i (x i) (x (i + 1)) := by
  obtain ⟨hx0, hmono, hxn, _, hrip⟩ := hx
  -- bounds on the cut points
  have hbd : ∀ k, k ≤ n → 0 ≤ x k ∧ x k ≤ x n := by
    have h1 : ∀ k, k ≤ n → 0 ≤ x k := by
      intro k
      induction k with
      | zero => intro _; rw [hx0]
      | succ k ih => intro hk; exact le_trans (ih (by omega)) (hmono k (by omega))
    have h2 : ∀ m k, k + m = n → x k ≤ x n := by
      intro m
      induction m with
      | zero => intro k hk; simp at hk; subst hk; exact le_refl _
      | succ m ih =>
        intro k hk
        exact le_trans (hmono k (by omega)) (ih (k + 1) (by omega))
    intro k hk
    exact ⟨h1 k hk, h2 (n - k) k (by omega)⟩
  have hin : ∀ k, k ≤ n → x k ∈ Set.Icc (0:ℝ) 1 := fun k hk =>
    ⟨(hbd k hk).1, le_trans (hbd k hk).2 hxn⟩
  -- nonpositivity of reversed intervals
  have hrev : ∀ m (hm : m < n) (a b : ℝ), a ∈ Set.Icc (0:ℝ) 1 → b ∈ Set.Icc (0:ℝ) 1 →
      b ≤ a → val f m a b ≤ 0 := by
    intro m hm a b ha hb hba
    rw [val_eq f m hm, intervalIntegral.integral_symm]
    have : 0 ≤ ∫ t in b..a, f ⟨m, hm⟩ t := by
      apply intervalIntegral.integral_nonneg hba
      intro u hu
      exact (hf ⟨m, hm⟩).1 u ⟨le_trans hb.1 hu.1, le_trans hu.2 ha.2⟩
    linarith
  -- strictness from ripple positivity
  have hstrict : ∀ m, m + 1 < n → x m < x (m + 1) ∧ x (m + 1) < x (m + 2) := by
    intro m hm
    obtain ⟨heq, hpos⟩ := hrip m hm
    constructor
    · by_contra hcon
      push Not at hcon
      have := hrev m (by omega) _ _ (hin m (by omega)) (hin (m + 1) (by omega)) hcon
      linarith
    · by_contra hcon
      push Not at hcon
      have := hrev m (by omega) _ _ (hin (m + 1) (by omega)) (hin (m + 2) (by omega)) hcon
      linarith
  -- positivity of every agent's value on a nondegenerate interval
  have hposval : ∀ p (hp : p < n) (a b : ℝ), 0 ≤ a → a < b → b ≤ 1 → 0 < val f p a b := by
    intro p hp a b ha hab hb
    rw [val_eq f p hp]
    apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ hab
    · have hI := (hf ⟨p, hp⟩).2.2.1
      exact hI.mono_set (by
        rw [Set.uIcc_of_le hab.le, Set.uIcc_of_le zero_le_one]
        exact Set.Icc_subset_Icc ha hb)
    · intro u hu
      exact hmlrp.1 ⟨p, hp⟩ u ⟨by linarith [hu.1], by linarith [hu.2]⟩
  -- the key ratio inequality from Lemma 1 (i)
  have hkey : ∀ p q m, p ≤ q → q < n → m + 1 < n →
      val f q (x m) (x (m + 1)) / val f p (x m) (x (m + 1)) ≤
        val f q (x (m + 1)) (x (m + 2)) / val f p (x (m + 1)) (x (m + 2)) := by
    intro p q m hpq hq hm
    have hp : p < n := by omega
    have L1 := (MLRPCake.EnvyFree.lemma_1 (f ⟨p, hp⟩) (f ⟨q, hq⟩) (hf _) (hf _)
      (hmlrp.1 _) (hmlrp.1 _)
      (fun b c hb hbc hc => ratio_mono f hmlrp (q - p) p q hp hq (by omega) b c hb hbc hc)).1
    have := L1 (x m) (x (m + 1)) (x (m + 1)) (x (m + 2)) (hin m (by omega)).1
      (hstrict m hm).1.le le_rfl (hstrict m hm).2 (hin (m + 2) (by omega)).2
    simpa only [val_eq f p hp, val_eq f q hq] using this
  -- left chain
  have hleft : ∀ i k, i < n → k < i → val f i (x k) (x (k + 1)) ≤ val f i (x (k + 1)) (x (k + 2)) := by
    intro i k hi hki
    have hk : k + 1 < n := by omega
    have h := hkey k i k hki.le hi hk
    obtain ⟨heq, hpos⟩ := hrip k hk
    rw [← heq] at h
    exact (div_le_div_iff_of_pos_right hpos).1 h
  -- right chain
  have hright : ∀ i j, i ≤ j → j + 1 < n →
      val f i (x (j + 1)) (x (j + 2)) ≤ val f i (x j) (x (j + 1)) := by
    intro i j hij hj
    have hi : i < n := by omega
    have h := hkey i j j hij (by omega) hj
    obtain ⟨heq, hpos⟩ := hrip j hj
    rw [← heq] at h
    have hA : 0 < val f i (x j) (x (j + 1)) :=
      hposval i hi _ _ (hin j (by omega)).1 (hstrict j hj).1 (hin (j + 1) (by omega)).2
    have hB : 0 < val f i (x (j + 1)) (x (j + 2)) :=
      hposval i hi _ _ (hin (j + 1) (by omega)).1 (hstrict j hj).2 (hin (j + 2) (by omega)).2
    exact (div_le_div_iff_of_pos_left hpos hA hB).1 h
  intro i j hi hj
  rcases le_or_gt j i with hji | hij
  · -- j ≤ i: climb from j to i
    have : ∀ m, j + m ≤ i → val f i (x j) (x (j + 1)) ≤ val f i (x (j + m)) (x (j + m + 1)) := by
      intro m
      induction m with
      | zero => intro _; simp
      | succ m ih =>
        intro hm
        have := hleft i (j + m) hi (by omega)
        have e1 : j + (m + 1) = j + m + 1 := by omega
        have e2 : j + m + 1 + 1 = j + m + 2 := by omega
        rw [e1, e2]
        exact le_trans (ih (by omega)) this
    have h := this (i - j) (by omega)
    have e : j + (i - j) = i := by omega
    rwa [e] at h
  · -- i < j: descend from i to j
    have : ∀ m, i + m < n → val f i (x (i + m)) (x (i + m + 1)) ≤ val f i (x i) (x (i + 1)) := by
      intro m
      induction m with
      | zero => intro _; simp
      | succ m ih =>
        intro hm
        have := hright i (i + m) (by omega) (by omega)
        have e1 : i + (m + 1) = i + m + 1 := by omega
        have e2 : i + m + 1 + 1 = i + m + 2 := by omega
        rw [e1, e2]
        exact le_trans this (ih (by omega))
    have h := this (j - i) (by omega)
    have e : i + (j - i) = j := by omega
    rwa [e] at h
