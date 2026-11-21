-- Prove2me | solution 1 for MaskedLinx.display_19_b_pos
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T03:46:35.158002+00:00
-- url     : https://prove2.me/submissions/342fa18b-cf4e-4ccd-9576-7cef59a16de7

import Mathlib

set_option maxHeartbeats 2000000

theorem solution (c₁ c₂ : ℝ) (h₁ : c₁ ^ 2 ≤ 1) (h₂ : c₂ ^ 2 ≤ 1) (hne : c₁ ^ 2 ≠ c₂ ^ 2) :
    let φ : ℝ → ℝ := fun γ =>
      Real.log ((1 - c₁ ^ 2) ^ 2 / 4 * γ + (1 + c₁ ^ 2) / 2 + 1 / (4 * γ)) +
      Real.log ((1 - c₂ ^ 2) ^ 2 / 4 * γ + (1 + c₂ ^ 2) / 2 + 1 / (4 * γ))
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ (∀ γ : ℝ, 0 < γ → φ γ₀ ≤ φ γ) ∧ 0 < φ γ₀ := by
  dsimp only
  set f : ℝ → ℝ := fun γ =>
    Real.log ((1 - c₁ ^ 2) ^ 2 / 4 * γ + (1 + c₁ ^ 2) / 2 + 1 / (4 * γ)) +
    Real.log ((1 - c₂ ^ 2) ^ 2 / 4 * γ + (1 + c₂ ^ 2) / 2 + 1 / (4 * γ)) with hf
  have hfe : ∀ γ : ℝ, f γ =
      Real.log ((1 - c₁ ^ 2) ^ 2 / 4 * γ + (1 + c₁ ^ 2) / 2 + 1 / (4 * γ)) +
      Real.log ((1 - c₂ ^ 2) ^ 2 / 4 * γ + (1 + c₂ ^ 2) / 2 + 1 / (4 * γ)) := by
    intro γ
    simp only [hf]
  -- the key algebraic identity
  have hid : ∀ (c : ℝ) {γ : ℝ}, γ ≠ 0 →
      4 * γ * (((1 - c ^ 2) ^ 2 / 4) * γ + (1 + c ^ 2) / 2 + 1 / (4 * γ) - 1)
        = ((1 - c ^ 2) * γ - 1) ^ 2 := by
    intro c γ hγ
    field_simp
    ring
  have key_ge : ∀ (c γ : ℝ), 0 < γ →
      1 ≤ (1 - c ^ 2) ^ 2 / 4 * γ + (1 + c ^ 2) / 2 + 1 / (4 * γ) := by
    intro c γ hγ
    have h := hid c hγ.ne'
    nlinarith [sq_nonneg ((1 - c ^ 2) * γ - 1), h, hγ]
  have key_gt : ∀ (c γ : ℝ), 0 < γ → (1 - c ^ 2) * γ ≠ 1 →
      1 < (1 - c ^ 2) ^ 2 / 4 * γ + (1 + c ^ 2) / 2 + 1 / (4 * γ) := by
    intro c γ hγ hne'
    have h := hid c hγ.ne'
    have hpos : 0 < ((1 - c ^ 2) * γ - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne')
    nlinarith [h, hγ, hpos]
  have key_eq : ∀ (c γ : ℝ), 0 < γ → (1 - c ^ 2) * γ = 1 →
      (1 - c ^ 2) ^ 2 / 4 * γ + (1 + c ^ 2) / 2 + 1 / (4 * γ) = 1 := by
    intro c γ hγ h
    have hkey := hid c hγ.ne'
    rw [h] at hkey
    have hzero : 4 * γ * (((1 - c ^ 2) ^ 2 / 4) * γ + (1 + c ^ 2) / 2 + 1 / (4 * γ) - 1) = 0 := by
      rw [hkey]; ring
    have h4 : 4 * γ ≠ 0 := by positivity
    rcases mul_eq_zero.mp hzero with h' | h'
    · exact absurd h' h4
    · linarith
  -- positivity of the two factors
  have hprod : ∀ γ : ℝ, 0 < γ →
      1 < ((1 - c₁ ^ 2) ^ 2 / 4 * γ + (1 + c₁ ^ 2) / 2 + 1 / (4 * γ)) *
          ((1 - c₂ ^ 2) ^ 2 / 4 * γ + (1 + c₂ ^ 2) / 2 + 1 / (4 * γ)) := by
    intro γ hγ
    by_cases h1 : (1 - c₁ ^ 2) * γ = 1
    · have hX1 := key_eq c₁ γ hγ h1
      have h2 : (1 - c₂ ^ 2) * γ ≠ 1 := by
        intro h2
        apply hne
        have : (1 - c₁ ^ 2) * γ = (1 - c₂ ^ 2) * γ := by rw [h1, h2]
        nlinarith [this, hγ]
      have hYg := key_gt c₂ γ hγ h2
      rw [hX1, one_mul]
      exact hYg
    · have hXg := key_gt c₁ γ hγ h1
      have hYg := key_ge c₂ γ hγ
      nlinarith
  have hfpos : ∀ γ : ℝ, 0 < γ → 0 < f γ := by
    intro γ hγ
    have hX := key_ge c₁ γ hγ
    have hY := key_ge c₂ γ hγ
    have hp := hprod γ hγ
    have hX0 : 0 < (1 - c₁ ^ 2) ^ 2 / 4 * γ + (1 + c₁ ^ 2) / 2 + 1 / (4 * γ) :=
      lt_of_lt_of_le zero_lt_one hX
    have hY0 : 0 < (1 - c₂ ^ 2) ^ 2 / 4 * γ + (1 + c₂ ^ 2) / 2 + 1 / (4 * γ) :=
      lt_of_lt_of_le zero_lt_one hY
    rw [hfe γ, ← Real.log_mul hX0.ne' hY0.ne']
    exact Real.log_pos hp
  have hf1 : 0 ≤ f 1 := by
    have hX := key_ge c₁ 1 one_pos
    have hY := key_ge c₂ 1 one_pos
    rw [hfe 1]
    have h1' : 0 ≤ Real.log ((1 - c₁ ^ 2) ^ 2 / 4 * 1 + (1 + c₁ ^ 2) / 2 + 1 / (4 * 1)) :=
      Real.log_nonneg hX
    have h2' : 0 ≤ Real.log ((1 - c₂ ^ 2) ^ 2 / 4 * 1 + (1 + c₂ ^ 2) / 2 + 1 / (4 * 1)) :=
      Real.log_nonneg hY
    linarith
  -- continuity
  have hcont : ContinuousOn f (Set.Ioi 0) := by
    have hXc : ContinuousOn (fun γ : ℝ =>
        (1 - c₁ ^ 2) ^ 2 / 4 * γ + (1 + c₁ ^ 2) / 2 + 1 / (4 * γ)) (Set.Ioi 0) := by
      apply ContinuousOn.add
      · have h : Continuous fun γ : ℝ => (1 - c₁ ^ 2) ^ 2 / 4 * γ + (1 + c₁ ^ 2) / 2 :=
          (continuous_const.mul continuous_id).add continuous_const
        exact h.continuousOn
      · have h : ContinuousOn (fun γ : ℝ => (4 * γ)⁻¹) (Set.Ioi 0) := by
          apply ContinuousOn.inv₀
          · exact (continuous_const.mul continuous_id).continuousOn
          · intro γ hγ
            have hγ0 : (0 : ℝ) < γ := hγ
            positivity
        simpa [one_div] using h
    have hYc : ContinuousOn (fun γ : ℝ =>
        (1 - c₂ ^ 2) ^ 2 / 4 * γ + (1 + c₂ ^ 2) / 2 + 1 / (4 * γ)) (Set.Ioi 0) := by
      apply ContinuousOn.add
      · have h : Continuous fun γ : ℝ => (1 - c₂ ^ 2) ^ 2 / 4 * γ + (1 + c₂ ^ 2) / 2 :=
          (continuous_const.mul continuous_id).add continuous_const
        exact h.continuousOn
      · have h : ContinuousOn (fun γ : ℝ => (4 * γ)⁻¹) (Set.Ioi 0) := by
          apply ContinuousOn.inv₀
          · exact (continuous_const.mul continuous_id).continuousOn
          · intro γ hγ
            have hγ0 : (0 : ℝ) < γ := hγ
            positivity
        simpa [one_div] using h
    have : f = fun γ => Real.log ((1 - c₁ ^ 2) ^ 2 / 4 * γ + (1 + c₁ ^ 2) / 2 + 1 / (4 * γ)) +
        Real.log ((1 - c₂ ^ 2) ^ 2 / 4 * γ + (1 + c₂ ^ 2) / 2 + 1 / (4 * γ)) := by
      funext γ; exact hfe γ
    rw [this]
    exact (hXc.log (fun γ hγ => (lt_of_lt_of_le zero_lt_one (key_ge c₁ γ hγ)).ne')).add
      (hYc.log (fun γ hγ => (lt_of_lt_of_le zero_lt_one (key_ge c₂ γ hγ)).ne'))
  -- small gamma
  have hsmall : ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ∀ γ : ℝ, 0 < γ → γ < a → f 1 < f γ := by
    refine ⟨1 / (4 * Real.exp (f 1 / 2 + 1)), ?_, ?_, ?_⟩
    · positivity
    · have hexp : (1 : ℝ) ≤ Real.exp (f 1 / 2 + 1) := Real.one_le_exp (by linarith)
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * Real.exp (f 1 / 2 + 1))]
      nlinarith [Real.exp_pos (f 1 / 2 + 1)]
    · intro γ hγ hγa
      have hXle : 1 / (4 * γ) ≤ (1 - c₁ ^ 2) ^ 2 / 4 * γ + (1 + c₁ ^ 2) / 2 + 1 / (4 * γ) := by
        have hA : 0 ≤ (1 - c₁ ^ 2) ^ 2 / 4 * γ := by positivity
        have hB : 0 ≤ (1 + c₁ ^ 2) / 2 := by positivity
        linarith
      have hYle : 1 / (4 * γ) ≤ (1 - c₂ ^ 2) ^ 2 / 4 * γ + (1 + c₂ ^ 2) / 2 + 1 / (4 * γ) := by
        have hA : 0 ≤ (1 - c₂ ^ 2) ^ 2 / 4 * γ := by positivity
        have hB : 0 ≤ (1 + c₂ ^ 2) / 2 := by positivity
        linarith
      have hlogX : Real.log (1 / (4 * γ)) ≤
          Real.log ((1 - c₁ ^ 2) ^ 2 / 4 * γ + (1 + c₁ ^ 2) / 2 + 1 / (4 * γ)) :=
        Real.log_le_log (by positivity) hXle
      have hlogY : Real.log (1 / (4 * γ)) ≤
          Real.log ((1 - c₂ ^ 2) ^ 2 / 4 * γ + (1 + c₂ ^ 2) / 2 + 1 / (4 * γ)) :=
        Real.log_le_log (by positivity) hYle
      have hexp2 : Real.exp (f 1 / 2 + 1) < 1 / (4 * γ) := by
        have h4e : 0 < 4 * Real.exp (f 1 / 2 + 1) := by positivity
        rw [lt_div_iff₀ h4e] at hγa
        rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * γ)]
        nlinarith
      have hlog : f 1 / 2 + 1 < Real.log (1 / (4 * γ)) := by
        have h := Real.log_lt_log (Real.exp_pos (f 1 / 2 + 1)) hexp2
        rwa [Real.log_exp] at h
      rw [hfe γ]
      linarith
  -- large gamma
  have hlarge : ∃ b : ℝ, 1 ≤ b ∧ ∀ γ : ℝ, b < γ → f 1 < f γ := by
    have hcase : 0 < (1 - c₁ ^ 2) ^ 2 / 4 ∨ 0 < (1 - c₂ ^ 2) ^ 2 / 4 := by
      by_contra hcon
      push_neg at hcon
      have ha1 : (1 - c₁ ^ 2) ^ 2 / 4 = 0 := le_antisymm hcon.1 (by positivity)
      have ha2 : (1 - c₂ ^ 2) ^ 2 / 4 = 0 := le_antisymm hcon.2 (by positivity)
      apply hne
      have hc1 : (1 - c₁ ^ 2) ^ 2 = 0 := by nlinarith
      have hc2 : (1 - c₂ ^ 2) ^ 2 = 0 := by nlinarith
      nlinarith [sq_nonneg (1 - c₁ ^ 2), sq_nonneg (1 - c₂ ^ 2)]
    rcases hcase with hA | hA
    · refine ⟨max 1 (Real.exp (f 1) / ((1 - c₁ ^ 2) ^ 2 / 4)), le_max_left _ _, ?_⟩
      intro γ hγ
      have hγexp : Real.exp (f 1) / ((1 - c₁ ^ 2) ^ 2 / 4) < γ :=
        lt_of_le_of_lt (le_max_right _ _) hγ
      have hXbig : Real.exp (f 1) <
          (1 - c₁ ^ 2) ^ 2 / 4 * γ + (1 + c₁ ^ 2) / 2 + 1 / (4 * γ) := by
        have hγ0 : (0 : ℝ) < γ := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) hγ.le)
        have h1 : (1 + c₁ ^ 2) / 2 + 1 / (4 * γ) ≥ 0 := by positivity
        have h2 : Real.exp (f 1) < (1 - c₁ ^ 2) ^ 2 / 4 * γ := by
          rw [div_lt_iff₀ hA] at hγexp
          linarith
        linarith
      have hlogX : f 1 < Real.log ((1 - c₁ ^ 2) ^ 2 / 4 * γ + (1 + c₁ ^ 2) / 2 + 1 / (4 * γ)) := by
        have h := Real.log_lt_log (Real.exp_pos (f 1)) hXbig
        rwa [Real.log_exp] at h
      have hγ0 : (0 : ℝ) < γ := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) hγ.le)
      have hYge := key_ge c₂ γ hγ0
      have hlogY : 0 ≤ Real.log ((1 - c₂ ^ 2) ^ 2 / 4 * γ + (1 + c₂ ^ 2) / 2 + 1 / (4 * γ)) :=
        Real.log_nonneg hYge
      rw [hfe γ]
      linarith
    · refine ⟨max 1 (Real.exp (f 1) / ((1 - c₂ ^ 2) ^ 2 / 4)), le_max_left _ _, ?_⟩
      intro γ hγ
      have hγexp : Real.exp (f 1) / ((1 - c₂ ^ 2) ^ 2 / 4) < γ :=
        lt_of_le_of_lt (le_max_right _ _) hγ
      have hγ0 : (0 : ℝ) < γ := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) hγ.le)
      have hYbig : Real.exp (f 1) <
          (1 - c₂ ^ 2) ^ 2 / 4 * γ + (1 + c₂ ^ 2) / 2 + 1 / (4 * γ) := by
        have h1 : (1 + c₂ ^ 2) / 2 + 1 / (4 * γ) ≥ 0 := by positivity
        have h2 : Real.exp (f 1) < (1 - c₂ ^ 2) ^ 2 / 4 * γ := by
          rw [div_lt_iff₀ hA] at hγexp
          linarith
        linarith
      have hlogY : f 1 < Real.log ((1 - c₂ ^ 2) ^ 2 / 4 * γ + (1 + c₂ ^ 2) / 2 + 1 / (4 * γ)) := by
        have h := Real.log_lt_log (Real.exp_pos (f 1)) hYbig
        rwa [Real.log_exp] at h
      have hXge := key_ge c₁ γ hγ0
      have hlogX : 0 ≤ Real.log ((1 - c₁ ^ 2) ^ 2 / 4 * γ + (1 + c₁ ^ 2) / 2 + 1 / (4 * γ)) :=
        Real.log_nonneg hXge
      rw [hfe γ]
      linarith
  -- assemble
  obtain ⟨a, ha0, ha1, ha⟩ := hsmall
  obtain ⟨b, hb1, hb⟩ := hlarge
  have hab : a ≤ b := le_trans ha1 hb1
  have hcont' : ContinuousOn f (Set.Icc a b) :=
    hcont.mono (fun x hx => lt_of_lt_of_le ha0 hx.1)
  have hne' : (Set.Icc a b).Nonempty := ⟨a, le_rfl, hab⟩
  obtain ⟨γ₀, hγ₀mem, hmin⟩ := isCompact_Icc.exists_isMinOn hne' hcont'
  have hγ₀ : 0 < γ₀ := lt_of_lt_of_le ha0 hγ₀mem.1
  have h1mem : (1 : ℝ) ∈ Set.Icc a b := ⟨ha1, hb1⟩
  have hmin1 : f γ₀ ≤ f 1 := hmin h1mem
  refine ⟨γ₀, hγ₀, ?_, hfpos γ₀ hγ₀⟩
  intro γ hγ
  rcases lt_or_ge γ a with h | h
  · exact le_trans hmin1 (le_of_lt (ha γ hγ h))
  · rcases le_or_gt γ b with h' | h'
    · exact hmin ⟨h, h'⟩
    · exact le_trans hmin1 (le_of_lt (hb γ h'))
