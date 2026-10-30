-- Prove2me | solution 1 for OAI.Falconer.profile_contact_interval
-- status  : ACCEPTED   (prove)
-- author  : @dangnguyen
-- created : 2026-10-29T19:23:44.495696+00:00
-- url     : https://prove2.me/submissions/1c941053-767e-4713-8cdc-c13c3872fb5a

import Mathlib

set_option autoImplicit false

open Set
open scoped NNReal

/-!
# A contact interval

Formalization of the lemma "A contact interval" (`prep:contact`).

Reading of the informal statement:
* `m : [0,1] → ℝ` is encoded as `m : ℝ → ℝ` with every hypothesis on `m` imposed only on
  `Icc 0 1`; values of `m` outside `[0,1]` are irrelevant and never used.
* "Lipschitz" means Lipschitz on `[0,1]` with some (unspecified) constant `K`.
* `m(u) ≥ s u` is assumed for every `u ∈ [0,1]` (the whole domain of `m`).
* `q, t, s` are arbitrary reals with `q < t < s`; no sign condition is imposed.
-/

/-- **A contact interval.** If `m` is Lipschitz on `[0,1]`, `m 0 = 0` and
`m u ≥ s u` on `[0,1]`, then for `q < t < s` there are `0 < A < B < 1` with `B < 2A` such that
`m w ≥ q w` on `[0,A]`, `m w - m A ≥ t (w - A)` on `[A,B]` and `m w - m B ≥ q (w - B)` on `[B,1]`. -/
theorem contact_interval_core (m : ℝ → ℝ) (q t s : ℝ)
    (hlip : ∃ K : NNReal, LipschitzOnWith K m (Icc 0 1))
    (h0 : m 0 = 0)
    (hs : ∀ u ∈ Icc (0 : ℝ) 1, s * u ≤ m u)
    (hqt : q < t) (hts : t < s) :
    ∃ A B : ℝ, 0 < A ∧ A < B ∧ B < 1 ∧ B < 2 * A ∧
      (∀ w ∈ Icc 0 A, q * w ≤ m w) ∧
      (∀ w ∈ Icc A B, t * (w - A) ≤ m w - m A) ∧
      (∀ w ∈ Icc B 1, q * (w - B) ≤ m w - m B) := by
  obtain ⟨K, hK⟩ := hlip
  have hcont : ContinuousOn m (Icc 0 1) := hK.continuousOn
  -- `g u = m u - q u`, as in the paper
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, ∀ w, g w = m w - q * w := ⟨_, fun _ => rfl⟩
  have hg_eq : g = fun w => m w - q * w := funext hg
  have hgc : ContinuousOn g (Icc 0 1) := by
    rw [hg_eq]; exact hcont.sub (continuousOn_const.mul continuousOn_id)
  have hc : 0 < t - q := sub_pos.2 hqt
  -- `P u` is a minimizer of `g` on `[u,1]`, so `F u = g (P u)` in the paper's notation
  have hmin : ∀ u : ℝ, ∃ p, 0 ≤ u → u ≤ 1 → (p ∈ Icc u 1 ∧ ∀ y ∈ Icc u 1, g p ≤ g y) := by
    intro u
    by_cases hu : 0 ≤ u ∧ u ≤ 1
    · obtain ⟨p, hp, hpm⟩ := (isCompact_Icc : IsCompact (Icc u 1)).exists_isMinOn
        (nonempty_Icc.2 hu.2) (hgc.mono (Icc_subset_Icc_left hu.1))
      exact ⟨p, fun _ _ => ⟨hp, fun y hy => isMinOn_iff.mp hpm y hy⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hu⟩
  choose P hP using hmin
  -- Key step: a definite increase of `F` between nearby points `v < u` yields `A` and `B`.
  have key : ∀ u v : ℝ, 0 < v → v < u → u ≤ 1 / 2 → 3 * u ≤ 4 * v →
      (t - q) * (u - v) ≤ g (P u) - g (P v) →
      ∃ A B : ℝ, 0 < A ∧ A < B ∧ B < 1 ∧ B < 2 * A ∧
        (∀ w ∈ Icc 0 A, q * w ≤ m w) ∧
        (∀ w ∈ Icc A B, t * (w - A) ≤ m w - m A) ∧
        (∀ w ∈ Icc B 1, q * (w - B) ≤ m w - m B) := by
    intro u v hv hvu hu1 huv hgap
    obtain ⟨⟨hxv, hx1⟩, hxmin⟩ := hP v hv.le (by linarith)
    obtain ⟨-, humin⟩ := hP u (by linarith) (by linarith)
    have hpos : 0 < (t - q) * (u - v) := mul_pos hc (sub_pos.2 hvu)
    -- the minimizer `x` of `g` on `[v,1]` lies to the left of `u`
    have hxu : P v < u := by
      by_contra hcon
      push Not at hcon
      have := humin (P v) ⟨hcon, hx1⟩
      linarith
    have hLu : g (P u) ≤ g u := humin u ⟨le_rfl, by linarith⟩
    have hxL : g (P v) ≤ g (P u) := by linarith
    have hsub : ∀ a, 0 ≤ a → Icc a u ⊆ Icc 0 1 := fun a ha => Icc_subset_Icc ha (by linarith)
    have ivt : ∀ y, 0 ≤ y → y ≤ u → g y ≤ g (P u) → ∃ z ∈ Icc y u, g z = g (P u) := by
      intro y hy0 hyu hyL
      exact intermediate_value_Icc hyu (hgc.mono (hsub y hy0)) ⟨hyL, hLu⟩
    -- `B` is the last point of `[x,u]` where `g` takes the value `F u`; it is a contact point
    have hT_closed : IsClosed (Icc (P v) u ∩ g ⁻¹' {g (P u)}) :=
      (hgc.mono (hsub (P v) (by linarith))).preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_singleton
    have hT_ne : (Icc (P v) u ∩ g ⁻¹' {g (P u)}).Nonempty := by
      obtain ⟨z, hz, hz'⟩ := ivt (P v) (by linarith) hxu.le hxL
      exact ⟨z, hz, hz'⟩
    have hT_bdd : BddAbove (Icc (P v) u ∩ g ⁻¹' {g (P u)}) := ⟨u, fun z hz => hz.1.2⟩
    obtain ⟨B, hBdef⟩ : ∃ B, B = sSup (Icc (P v) u ∩ g ⁻¹' {g (P u)}) := ⟨_, rfl⟩
    have hBT : B ∈ Icc (P v) u ∩ g ⁻¹' {g (P u)} := hBdef ▸ hT_closed.csSup_mem hT_ne hT_bdd
    have hBx : P v ≤ B := hBT.1.1
    have hBu : B ≤ u := hBT.1.2
    have hgB : g B = g (P u) := hBT.2
    have hcontact : ∀ y ∈ Icc B 1, g B ≤ g y := by
      intro y hy
      rw [hgB]
      by_cases hyu : u ≤ y
      · exact humin y ⟨hyu, hy.2⟩
      · push Not at hyu
        by_contra hlt
        push Not at hlt
        obtain ⟨z, hz, hzL⟩ := ivt y (by linarith [hy.1]) hyu.le hlt.le
        have hzT : z ∈ Icc (P v) u ∩ g ⁻¹' {g (P u)} :=
          ⟨⟨by linarith [hz.1, hy.1], hz.2⟩, hzL⟩
        have hzB : z ≤ B := hBdef ▸ le_csSup hT_bdd hzT
        have hzy : z = y := le_antisymm (by linarith [hy.1]) hz.1
        rw [hzy] at hzL
        linarith
    have hgap' : (t - q) * (B - P v) ≤ g B - g (P v) := by
      have : (t - q) * (B - P v) ≤ (t - q) * (u - v) :=
        mul_le_mul_of_nonneg_left (by linarith) hc.le
      linarith
    have hxB : P v < B := by
      rcases eq_or_lt_of_le hBx with h | h
      · exfalso; rw [← h] at hgB; linarith
      · exact h
    -- `A` minimizes `m w - t w` on `[x,B]`, chosen different from `B`
    obtain ⟨h, hh⟩ : ∃ h : ℝ → ℝ, ∀ w, h w = g w - (t - q) * w := ⟨_, fun _ => rfl⟩
    have hh_eq : h = fun w => g w - (t - q) * w := funext hh
    have hhc : ContinuousOn h (Icc (P v) B) := by
      rw [hh_eq]
      exact (hgc.mono (Icc_subset_Icc (by linarith) (by linarith))).sub
        (continuousOn_const.mul continuousOn_id)
    obtain ⟨A0, hA0, hA0min⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hBx) hhc
    have hA : ∃ A ∈ Icc (P v) B, A < B ∧ ∀ y ∈ Icc (P v) B, h A ≤ h y := by
      rcases eq_or_lt_of_le hA0.2 with hAB | hAB
      · refine ⟨P v, ⟨le_rfl, hBx⟩, hxB, fun y hy => ?_⟩
        have h1 : h (P v) ≤ h B := by rw [hh, hh]; linarith
        have h2 := isMinOn_iff.mp hA0min y hy
        rw [hAB] at h2
        linarith
      · exact ⟨A0, hA0, hAB, isMinOn_iff.mp hA0min⟩
    obtain ⟨A, ⟨hxA, -⟩, hAB, hAmin⟩ := hA
    refine ⟨A, B, by linarith, hAB, by linarith, by linarith, ?_, ?_, ?_⟩
    · intro w hw
      have := hs w ⟨hw.1, by linarith [hw.2]⟩
      nlinarith [hw.1]
    · intro w hw
      have := hAmin w ⟨by linarith [hw.1], hw.2⟩
      rw [hh, hh, hg, hg] at this
      linarith
    · intro w hw
      have := hcontact w hw
      rw [hg, hg] at this
      linarith
  -- Telescoping along the geometric sequence `u k = (1/2) (3/4)^k`.
  have hpow_pos : ∀ k : ℕ, (0 : ℝ) < (3 / 4) ^ k := fun k => by positivity
  have hpow_le : ∀ k : ℕ, ((3 : ℝ) / 4) ^ k ≤ 1 := fun k => pow_le_one₀ (by norm_num) (by norm_num)
  have hF0 : (s - q) / 2 ≤ g (P (1 / 2)) := by
    obtain ⟨⟨hp1, hp2⟩, -⟩ := hP (1 / 2) (by norm_num) (by norm_num)
    have := hs (P (1 / 2)) ⟨by linarith, hp2⟩
    rw [hg]
    nlinarith
  have hFn : ∀ n : ℕ, g (P (1 / 2 * (3 / 4) ^ n)) ≤ (K - q) * (1 / 2 * (3 / 4) ^ n) := by
    intro n
    have h1 := hpow_pos n
    have h2 := hpow_le n
    obtain ⟨-, hmn⟩ := hP (1 / 2 * (3 / 4) ^ n) (by positivity) (by linarith)
    have h3 := hmn (1 / 2 * (3 / 4) ^ n) ⟨le_rfl, by linarith⟩
    have h4 := hK.dist_le_mul (1 / 2 * (3 / 4) ^ n) ⟨by positivity, by linarith⟩ 0
      ⟨le_rfl, zero_le_one⟩
    rw [Real.dist_eq, Real.dist_eq, h0, sub_zero, sub_zero,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 * (3 / 4) ^ n)] at h4
    have h5 := le_abs_self (m (1 / 2 * (3 / 4) ^ n))
    rw [hg (1 / 2 * (3 / 4) ^ n)] at h3
    linarith
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (t - q) * (1 / 2 * (3 / 4) ^ k - 1 / 2 * (3 / 4) ^ (k + 1)) ≤
      g (P (1 / 2 * (3 / 4) ^ k)) - g (P (1 / 2 * (3 / 4) ^ (k + 1))) := by
    by_contra hcon
    push Not at hcon
    have hsum : ∀ n : ℕ, g (P (1 / 2 * (3 / 4) ^ 0)) - g (P (1 / 2 * (3 / 4) ^ n)) ≤
        (t - q) * (1 / 2 * (3 / 4) ^ 0 - 1 / 2 * (3 / 4) ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => have := hcon n; linarith
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
      (show 0 < (s - t) / (|(K : ℝ) - t| + 1) by
        have : 0 < s - t := sub_pos.2 hts
        positivity)
      (show (3 / 4 : ℝ) < 1 by norm_num)
    rw [lt_div_iff₀ (by positivity)] at hn
    have h1 := hsum n
    have h2 := hFn n
    simp only [pow_zero, mul_one] at h1
    have h3 : ((K : ℝ) - t) * (3 / 4) ^ n ≤ |(K : ℝ) - t| * (3 / 4) ^ n :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (hpow_pos n).le
    nlinarith [hpow_pos n]
  have hk1 := hpow_pos k
  have hk2 := hpow_le k
  exact key (1 / 2 * (3 / 4) ^ k) (1 / 2 * (3 / 4) ^ (k + 1)) (by positivity)
    (by rw [pow_succ]; nlinarith) (by nlinarith) (by rw [pow_succ]; nlinarith) hk


/-- The target statement. The paper also assumes that `m` is nondecreasing; the proof does not use it. -/
theorem solution {m : ℝ → ℝ} {K : ℝ≥0} {q t s : ℝ}
    (hm : LipschitzOnWith K m (Icc 0 1)) (hzero : m 0 = 0)
    (hlower : ∀ u ∈ Icc (0:ℝ) 1, s*u ≤ m u) (hqt : q < t) (hts : t < s) :
    ∃ A B : ℝ, 0 < A ∧ A < B ∧ B < 1 ∧ B < 2*A ∧
      (∀ w ∈ Icc 0 A, q*w ≤ m w) ∧
      (∀ w ∈ Icc A B, t*(w-A) ≤ m w-m A) ∧
      (∀ w ∈ Icc B 1, q*(w-B) ≤ m w-m B) :=
  contact_interval_core m q t s ⟨K, hm⟩ hzero hlower hqt hts
