-- Prove2me | solution 1 for NonsmoothQN.Secant.secant_H_and_direction
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:46:40.319972+00:00
-- url     : https://prove2.me/submissions/44192d9d-de24-4886-b36b-7f66c92e1cd2

import Mathlib
import Definitions.Def_NonsmoothQN_Secant_Basic

set_option autoImplicit false
open NonsmoothQN.Secant

lemma lsStep_cases (A W : ℝ → Prop) (s : LSState) (hs : ¬(A s.t ∧ W s.t)) :
    (¬A s.t ∧ lsStep A W s = ⟨s.α, (s.t : WithTop ℝ), (s.α + s.t) / 2⟩) ∨
    (A s.t ∧ ¬W s.t ∧ s.β = ⊤ ∧ lsStep A W s = ⟨s.t, ⊤, 2 * s.t⟩) ∨
    (A s.t ∧ ¬W s.t ∧ ∃ b : ℝ, s.β = (b : WithTop ℝ) ∧
      lsStep A W s = ⟨s.t, (b : WithTop ℝ), (s.t + b) / 2⟩) := by
  classical
  obtain ⟨α, β, t⟩ := s
  by_cases hA : A t
  · have hW : ¬W t := fun hw => hs ⟨hA, hw⟩
    induction β using WithTop.recTopCoe with
    | top =>
      right; left
      refine ⟨hA, hW, rfl, ?_⟩
      simp [lsStep, hA, hW]
    | coe b =>
      right; right
      refine ⟨hA, hW, b, rfl, ?_⟩
      simp [lsStep, hA, hW]
  · left
    refine ⟨hA, ?_⟩
    simp [lsStep, hA]

lemma ls_term (A W : ℝ → Prop) (c : ℝ) (hc : 0 < c) (hA : ∀ t, A t ↔ t < 2 * c)
    (hW : ∀ t, W t ↔ c ≤ t) : lsTerminates A W := by
  by_contra hcon
  have hn : ∀ n, ¬(A (lsRun A W n).t ∧ W (lsRun A W n).t) := fun n h => hcon ⟨n, h⟩
  have hstep : ∀ n, lsRun A W (n + 1) = lsStep A W (lsRun A W n) := fun n => rfl
  have inv : ∀ n, 0 ≤ (lsRun A W n).α ∧ (lsRun A W n).α < c ∧ 0 < (lsRun A W n).t ∧
      ∀ b : ℝ, (lsRun A W n).β = (b : WithTop ℝ) → 2 * c ≤ b := by
    intro n
    induction n with
    | zero =>
      refine ⟨le_refl _, ?_, ?_, ?_⟩
      · show (0 : ℝ) < c; exact hc
      · show (0 : ℝ) < 1; exact one_pos
      · intro b hb; exact absurd hb (by simp [lsRun])
    | succ n ih =>
      obtain ⟨i1, i2, i3, i4⟩ := ih
      rw [hstep]
      rcases lsStep_cases A W _ (hn n) with ⟨hna, he⟩ | ⟨hna, hnw, hb, he⟩ | ⟨hna, hnw, b0, hb, he⟩
      · rw [he]
        refine ⟨i1, i2, by show 0 < ((lsRun A W n).α + (lsRun A W n).t) / 2; linarith, ?_⟩
        intro b hb
        have hb'' : (((lsRun A W n).t : ℝ) : WithTop ℝ) = ((b : ℝ) : WithTop ℝ) := hb
        have : (lsRun A W n).t = b := WithTop.coe_injective hb''
        rw [← this]
        by_contra hlt; push_neg at hlt
        exact hna ((hA _).2 hlt)
      · rw [he]
        have hlt : (lsRun A W n).t < c := by
          by_contra h; push_neg at h; exact hnw ((hW _).2 h)
        refine ⟨i3.le, hlt, by show 0 < 2 * (lsRun A W n).t; linarith, ?_⟩
        intro b hb; exact absurd hb (by simp)
      · rw [he]
        have hlt : (lsRun A W n).t < c := by
          by_contra h; push_neg at h; exact hnw ((hW _).2 h)
        have hb2 := i4 b0 hb
        refine ⟨i3.le, hlt, by show 0 < ((lsRun A W n).t + b0) / 2; linarith, ?_⟩
        intro b hb'
        have hb'' : ((b0 : ℝ) : WithTop ℝ) = ((b : ℝ) : WithTop ℝ) := hb'
        have : b0 = b := WithTop.coe_injective hb''
        subst this
        exact hb2
  by_cases hex : ∃ n, (lsRun A W n).β ≠ ⊤
  · classical
    let n0 := Nat.find hex
    have hn0 : (lsRun A W n0).β ≠ ⊤ := Nat.find_spec hex
    have hn0pos : n0 ≠ 0 := by
      intro h0
      apply hn0
      rw [h0]; rfl
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0pos
    have hmtop : (lsRun A W m).β = ⊤ := by
      by_contra hne
      exact Nat.find_min hex (show m < n0 by omega) hne
    have hm1 : (lsRun A W n0) = lsStep A W (lsRun A W m) := by rw [hm]; rfl
    obtain ⟨a0, b0, ha0, hb0, ht0⟩ : ∃ a b : ℝ, (lsRun A W n0).α = a ∧ (lsRun A W n0).β = (b : WithTop ℝ) ∧
        (lsRun A W n0).t = (a + b) / 2 := by
      rcases lsStep_cases A W _ (hn m) with ⟨hna, he⟩ | ⟨hna, hnw, hb, he⟩ | ⟨hna, hnw, b0, hb, he⟩
      · refine ⟨(lsRun A W m).α, (lsRun A W m).t, ?_, ?_, ?_⟩ <;> rw [hm1, he]
      · exfalso; apply hn0; rw [hm1, he]
      · exfalso; rw [hmtop] at hb; exact absurd hb (by simp)
    have key : ∀ j : ℕ, ∃ a b : ℝ, (lsRun A W (n0 + j)).α = a ∧ (lsRun A W (n0 + j)).β = (b : WithTop ℝ) ∧
        (lsRun A W (n0 + j)).t = (a + b) / 2 ∧ (b - a) * 2 ^ j = b0 - a0 := by
      intro j
      induction j with
      | zero => exact ⟨a0, b0, ha0, hb0, ht0, by simp⟩
      | succ j ih =>
        obtain ⟨a, b, h1, h2, h3, h4⟩ := ih
        have e : lsRun A W (n0 + (j + 1)) = lsStep A W (lsRun A W (n0 + j)) := rfl
        rcases lsStep_cases A W _ (hn (n0 + j)) with ⟨hna, he⟩ | ⟨hna, hnw, hb, he⟩ | ⟨hna, hnw, bb, hb, he⟩
        · refine ⟨a, (a + b) / 2, ?_, ?_, ?_, ?_⟩
          · rw [e, he, h1]
          · rw [e, he, h3]
          · rw [e, he, h3, h1]
          · rw [pow_succ]; nlinarith [h4]
        · exfalso; rw [h2] at hb; exact absurd hb (by simp)
        · have : bb = b := by rw [h2] at hb; exact_mod_cast hb.symm
          subst this
          refine ⟨(a + bb) / 2, bb, ?_, ?_, ?_, ?_⟩
          · rw [e, he, h3]
          · rw [e, he]
          · rw [e, he, h3]
          · rw [pow_succ]; nlinarith [h4]
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt ((b0 - a0) / c) (one_lt_two : (1 : ℝ) < 2)
    obtain ⟨a, b, h1, h2, h3, h4⟩ := key j
    obtain ⟨i1, i2, i3, i4⟩ := inv (n0 + j)
    have hb2 := i4 b h2
    rw [h1] at i2
    have hw : c < b - a := by linarith
    have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have : c * 2 ^ j ≤ (b - a) * 2 ^ j := by nlinarith
    rw [div_lt_iff₀ hc] at hj
    nlinarith
  · push_neg at hex
    have st : ∀ n, (lsRun A W n).t < c ∧ (lsRun A W (n + 1)).t = 2 * (lsRun A W n).t := by
      intro n
      rcases lsStep_cases A W _ (hn n) with ⟨hna, he⟩ | ⟨hna, hnw, hb, he⟩ | ⟨hna, hnw, bb, hb, he⟩
      · exfalso
        have h1 := hex (n + 1)
        rw [hstep, he] at h1
        exact absurd h1 (by simp)
      · refine ⟨?_, ?_⟩
        · by_contra h; push_neg at h; exact hnw ((hW _).2 h)
        · rw [hstep, he]
      · exfalso; rw [hex n] at hb; exact absurd hb (by simp)
    have tpow : ∀ n, (lsRun A W n).t = 2 ^ n := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [(st n).2, ih]; ring
    obtain ⟨n, hn'⟩ := pow_unbounded_of_one_lt c (one_lt_two : (1 : ℝ) < 2)
    have := (st n).1
    rw [tpow] at this
    linarith

lemma ls_result (A W : ℝ → Prop) (h : lsTerminates A W) : A (lsResult A W) ∧ W (lsResult A W) := by
  have := Nat.sInf_mem (s := {n : ℕ | A (lsRun A W n).t ∧ W (lsRun A W n).t}) h
  exact this

lemma step_size (s : SecState) (hx : s.x ≠ 0) (hH : 0 < s.H) :
    |s.x| ≤ secStepSize s * s.H ∧ secStepSize s * s.H < 2 * |s.x| := by
  have hc : 0 < |s.x| / s.H := div_pos (abs_pos.mpr hx) hH
  have e1 : -s.x / secDir s = |s.x| / s.H := by
    unfold secDir
    rcases lt_or_gt_of_ne hx with h | h
    · rw [Real.sign_of_neg h, abs_of_neg h]; field_simp
    · rw [Real.sign_of_pos h, abs_of_pos h]; field_simp
  have e2 : -2 * s.x / secDir s = 2 * (|s.x| / s.H) := by
    unfold secDir
    rcases lt_or_gt_of_ne hx with h | h
    · rw [Real.sign_of_neg h, abs_of_neg h]; field_simp
    · rw [Real.sign_of_pos h, abs_of_pos h]; field_simp
  have hAi : ∀ t, secA s.x (secDir s) t ↔ t < 2 * (|s.x| / s.H) := fun t => by
    unfold secA; rw [e2]
  have hWi : ∀ t, secW s.x (secDir s) t ↔ |s.x| / s.H ≤ t := fun t => by
    unfold secW; rw [e1]
  have hterm := ls_term (secA s.x (secDir s)) (secW s.x (secDir s)) (|s.x| / s.H) hc hAi hWi
  have hr := ls_result _ _ hterm
  have hA : secStepSize s < 2 * (|s.x| / s.H) := (hAi _).1 hr.1
  have hW : |s.x| / s.H ≤ secStepSize s := (hWi _).1 hr.2
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ hH] at hW; exact hW
  · have := mul_lt_mul_of_pos_right hA hH
    have e : 2 * (|s.x| / s.H) * s.H = 2 * |s.x| := by field_simp
    linarith

lemma spec (x H t : ℝ) (hx : x ≠ 0) (hH : 0 < H) (ht1 : |x| ≤ t * H) (ht2 : t * H < 2 * |x|)
    (hx' : x + t * (-H * Real.sign x) ≠ 0) :
    t * (-H * Real.sign x) / (Real.sign (x + t * (-H * Real.sign x)) - Real.sign x) = t * H / 2 ∧
    x * (x + t * (-H * Real.sign x)) < 0 := by
  rcases lt_or_gt_of_ne hx with h | h
  · rw [abs_of_neg h] at ht1 ht2
    rw [Real.sign_of_neg h] at hx' ⊢
    have hpos : 0 < x + t * (-H * -1) := by
      have : 0 ≤ x + t * (-H * -1) := by nlinarith
      exact lt_of_le_of_ne this (Ne.symm hx')
    rw [Real.sign_of_pos hpos]
    refine ⟨by field_simp; ring, by nlinarith⟩
  · rw [abs_of_pos h] at ht1 ht2
    rw [Real.sign_of_pos h] at hx' ⊢
    have hneg : x + t * (-H * 1) < 0 := by
      have : x + t * (-H * 1) ≤ 0 := by nlinarith
      exact lt_of_le_of_ne this hx'
    rw [Real.sign_of_neg hneg]
    refine ⟨by field_simp; ring, by nlinarith⟩

lemma step_pos (s : SecState) (hH : 0 < s.H) : 0 < (secStep s).H := by
  by_cases hx : s.x = 0
  · simp [secStep, hx, hH]
  · by_cases hx' : s.x + secStepSize s * secDir s = 0
    · simp [secStep, hx, hx', hH]
    · have hsz := step_size s hx hH
      have := (spec s.x s.H (secStepSize s) hx hH hsz.1 hsz.2 hx').1
      have hH' : (secStep s).H = secStepSize s * secDir s / (Real.sign (s.x + secStepSize s * secDir s) - Real.sign s.x) := by
        simp [secStep, hx, hx']
      rw [hH']
      unfold secDir
      rw [this]
      have h1 : 0 < |s.x| := abs_pos.mpr hx
      have : 0 < secStepSize s * s.H := lt_of_lt_of_le h1 hsz.1
      positivity

theorem solution (x₀ H₀ : ℝ) (hH₀ : 0 < H₀) (k : ℕ)
    (hk : secX x₀ H₀ k ≠ 0) (hk1 : secX x₀ H₀ (k + 1) ≠ 0) :
    secH x₀ H₀ (k + 1) = |secX x₀ H₀ (k + 1) - secX x₀ H₀ k| / 2 ∧
    secP x₀ H₀ (k + 1) =
      -(|secX x₀ H₀ (k + 1) - secX x₀ H₀ k| / 2) * Real.sign (secX x₀ H₀ (k + 1)) ∧
    secX x₀ H₀ k * secX x₀ H₀ (k + 1) < 0 := by
  have hpos : ∀ n, 0 < (secRun x₀ H₀ n).H := by
    intro n
    induction n with
    | zero => exact hH₀
    | succ n ih => exact step_pos _ ih
  set s := secRun x₀ H₀ k with hs
  have hrun : secRun x₀ H₀ (k + 1) = secStep s := rfl
  have hxk : s.x ≠ 0 := hk
  have hxk1 : (secStep s).x ≠ 0 := by
    have : secX x₀ H₀ (k + 1) = (secStep s).x := by unfold secX; rw [hrun]
    rw [← this]; exact hk1
  have hH := hpos k
  have hX : secX x₀ H₀ k = s.x := rfl
  have hX1 : secX x₀ H₀ (k + 1) = (secStep s).x := by unfold secX; rw [hrun]
  have hx' : s.x + secStepSize s * secDir s ≠ 0 := by
    intro h0
    apply hxk1
    simp [secStep, hxk, h0]
  have hsz := step_size s hxk hH
  have hsp := spec s.x s.H (secStepSize s) hxk hH hsz.1 hsz.2 hx'
  have hstep_x : (secStep s).x = s.x + secStepSize s * secDir s := by
    unfold secStep
    split_ifs <;> simp_all
  have hstep_H : (secStep s).H = secStepSize s * s.H / 2 := by
    have : (secStep s).H = secStepSize s * secDir s / (Real.sign (s.x + secStepSize s * secDir s) - Real.sign s.x) := by
      simp [secStep, hxk, hx']
    rw [this]; unfold secDir; exact hsp.1
  have hdiff : |(secStep s).x - s.x| = secStepSize s * s.H := by
    rw [hstep_x]
    have : s.x + secStepSize s * secDir s - s.x = secStepSize s * secDir s := by ring
    rw [this]; unfold secDir
    have ht : 0 ≤ secStepSize s := by
      by_contra hneg; push_neg at hneg
      have := mul_neg_of_neg_of_pos hneg hH
      linarith [hsz.1, abs_nonneg s.x]
    rcases lt_or_gt_of_ne hxk with h | h
    · rw [Real.sign_of_neg h]
      rw [show secStepSize s * (-s.H * -1) = secStepSize s * s.H by ring]
      exact abs_of_nonneg (by positivity)
    · rw [Real.sign_of_pos h]
      rw [show secStepSize s * (-s.H * 1) = -(secStepSize s * s.H) by ring]
      rw [abs_neg]; exact abs_of_nonneg (by positivity)
  rw [hX1, hX]
  refine ⟨?_, ?_, ?_⟩
  · show (secRun x₀ H₀ (k + 1)).H = _
    rw [hrun, hdiff, hstep_H]
  · show secDir (secRun x₀ H₀ (k + 1)) = _
    rw [hrun]
    unfold secDir
    rw [hdiff, hstep_H]
  · rw [hstep_x]; exact hsp.2
