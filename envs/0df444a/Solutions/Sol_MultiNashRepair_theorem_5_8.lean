-- Prove2me | solution 1 for MultiNashRepair.theorem_5_8
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T22:55:31.497202+00:00
-- url     : https://prove2.me/submissions/62848073-b2f1-4988-96c8-1226330cf0ff

import Mathlib
import Definitions.Def_MultiNashRepair_ScalarCertificate

open MultiNashRepair

theorem solution :
    (7 / 12 < fStar ∧ fStar < 3 / 5 ∧ 2 / 5 < sStar ∧ sStar < 5 / 12 ∧
      2 * fStar ^ 3 - 4 * fStar ^ 2 + 1 = 0) ∧
    (Hc sStar = sigmaStar ∧ sigmaStar = 9 - 16 * fStar + 6 * fStar ^ 2) ∧
    (119 / 75 < sigmaStar ∧ sigmaStar < 2 ∧ sigmaPoly sigmaStar = 0 ∧
      ∀ s ∈ Set.Ioo (1 : ℝ) 2, sigmaPoly s = 0 → s = sigmaStar) ∧
    (∀ H : ℝ, 0 ≤ H →
      Kf fStar H - sigmaStar = (2 * fStar - 1) * (H - sStar) ^ 2 / (fStar * (fStar + H))) ∧
    (∀ f : ℝ, 0 < f →
      sigmaStar - Kf f sStar = sigmaStar * (f - fStar) ^ 2 / (f * (f + sStar))) ∧
    (IsGreatest (U '' Set.Ioo 0 1) sigmaStar ∧
      (∀ f ∈ Set.Ioo (0 : ℝ) 1, U f = sigmaStar → f = fStar) ∧
      IsGreatest (Hc '' Set.Icc 0 (1 / 2)) sigmaStar) := by
  have hQdef : ∀ s, Qc s = 2 * s ^ 3 - 2 * s ^ 2 - 2 * s + 1 := fun s => rfl
  have hQcont : ContinuousOn Qc (Set.Icc (2/5 : ℝ) (5/12)) := by
    have : Qc = fun s => 2 * s ^ 3 - 2 * s ^ 2 - 2 * s + 1 := funext hQdef
    rw [this]; fun_prop
  obtain ⟨s0, hs0mem, hs0⟩ : ∃ s0 ∈ Set.Icc (2/5 : ℝ) (5/12), Qc s0 = 0 := by
    have h0 : (0:ℝ) ∈ Set.Icc (Qc (5/12)) (Qc (2/5)) := by
      rw [hQdef, hQdef]; constructor <;> norm_num
    obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc' (by norm_num : (2/5:ℝ) ≤ 5/12) hQcont h0
    exact ⟨c, hc, hfc⟩
  have hq0 : 2 * s0 ^ 3 - 2 * s0 ^ 2 - 2 * s0 + 1 = 0 := by rw [← hQdef]; exact hs0
  have hs0lo : 2/5 < s0 := by
    rcases eq_or_lt_of_le hs0mem.1 with h | h
    · rw [← h] at hq0; norm_num at hq0
    · exact h
  have hs0hi : s0 < 5/12 := by
    rcases eq_or_lt_of_le hs0mem.2 with h | h
    · rw [h] at hq0; norm_num at hq0
    · exact h
  have hanti : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1/2 → Qc b < Qc a := by
    intro a b ha hab hb
    have key : Qc a - Qc b = (b - a) * (2 + 2*(a+b) - 2*(a^2+a*b+b^2)) := by
      simp only [hQdef]; ring
    have : 0 < 2 + 2*(a+b) - 2*(a^2+a*b+b^2) := by nlinarith
    nlinarith [mul_pos (sub_pos.mpr hab) this]
  have hsS : sStar = s0 := by
    have : {s : ℝ | 0 ≤ s ∧ s ≤ 1 / 2 ∧ 0 ≤ Qc s} = Set.Icc 0 s0 := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_Icc]
      constructor
      · rintro ⟨h0, h1, h2⟩
        refine ⟨h0, ?_⟩
        by_contra hlt
        push Not at hlt
        have := hanti s0 s (by linarith) hlt h1
        linarith
      · rintro ⟨h0, h1⟩
        refine ⟨h0, by linarith, ?_⟩
        rcases eq_or_lt_of_le h1 with h | h
        · rw [h, hs0]
        · have := hanti s s0 h0 h (by linarith); linarith
    unfold sStar; rw [this, csSup_Icc (by linarith)]
  obtain ⟨σ0, hσ0⟩ : ∃ σ0 : ℝ, σ0 = 6 * s0 ^ 2 + 4 * s0 - 1 := ⟨_, rfl⟩
  have hσ0lo : 3/2 < σ0 := by rw [hσ0]; nlinarith
  have hσ0hi : σ0 < 2 := by rw [hσ0]; nlinarith
  have hPdef : ∀ s, sigmaPoly s = s ^ 3 - 19 * s ^ 2 + 27 * s + 1 := fun s => rfl
  have hPσ0 : sigmaPoly σ0 = 0 := by
    rw [hPdef, hσ0]; linear_combination (108 * s0 ^ 3 + 324 * s0 ^ 2 + 180 * s0 - 46) * hq0
  have hPanti : ∀ a b : ℝ, 1 ≤ a → a < b → b ≤ 2 → sigmaPoly b < sigmaPoly a := by
    intro a b ha hab hb
    have key : sigmaPoly a - sigmaPoly b = (b - a) * (19*(a+b) - 27 - (a^2+a*b+b^2)) := by
      simp only [hPdef]; ring
    have ha2 : a ≤ 2 := by linarith
    have hb1 : 1 ≤ b := by linarith
    have : 0 < 19*(a+b) - 27 - (a^2+a*b+b^2) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr ha2),
        mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hb),
        mul_nonneg (sub_nonneg.mpr ha2) (by linarith : (0:ℝ) ≤ b)]
    nlinarith [mul_pos (sub_pos.mpr hab) this]
  have hσS : sigmaStar = σ0 := by
    have : {s : ℝ | 1 ≤ s ∧ s ≤ 2 ∧ 0 ≤ sigmaPoly s} = Set.Icc 1 σ0 := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_Icc]
      constructor
      · rintro ⟨h0, h1, h2⟩
        refine ⟨h0, ?_⟩
        by_contra hlt; push Not at hlt
        have := hPanti σ0 s (by linarith) hlt h1; linarith
      · rintro ⟨h0, h1⟩
        refine ⟨h0, by linarith, ?_⟩
        rcases eq_or_lt_of_le h1 with h | h
        · rw [h, hPσ0]
        · have := hPanti s σ0 h0 h (by linarith); linarith
    unfold sigmaStar; rw [this, csSup_Icc (by linarith)]
  have hfS : fStar = 1 - s0 := by unfold fStar; rw [hsS]
  rw [hfS, hσS, hsS]
  -- (5.39)
  have p4 : ∀ H : ℝ, 0 ≤ H →
      Kf (1 - s0) H - σ0 = (2 * (1 - s0) - 1) * (H - s0) ^ 2 / ((1 - s0) * ((1 - s0) + H)) := by
    intro H hH
    have hden : (1 - s0) * ((1 - s0) + H) ≠ 0 := by
      have : 0 < (1 - s0) * ((1 - s0) + H) := by
        apply mul_pos <;> linarith
      exact this.ne'
    rw [Kf, eq_div_iff hden, sub_mul, div_mul_cancel₀ _ hden, hσ0]
    linear_combination (3 * H - 3 * s0 + 2) * hq0
  -- (5.40)
  have p5 : ∀ f : ℝ, 0 < f →
      σ0 - Kf f s0 = σ0 * (f - (1 - s0)) ^ 2 / (f * (f + s0)) := by
    intro f hf
    have hden : f * (f + s0) ≠ 0 := by
      have : 0 < f * (f + s0) := by apply mul_pos <;> linarith
      exact this.ne'
    rw [Kf, eq_div_iff hden, sub_mul, div_mul_cancel₀ _ hden, hσ0]
    linear_combination (-3 * f - 3 * s0 + 1) * hq0
  have hKbdd : ∀ f : ℝ, 0 < f → BddBelow (Kf f '' Set.Icc 0 f) := by
    intro f hf
    refine ⟨0, ?_⟩
    rintro _ ⟨H, ⟨hH0, hH1⟩, rfl⟩
    unfold Kf
    apply div_nonneg
    · apply mul_nonneg (by linarith)
      nlinarith
    · apply mul_nonneg (by linarith) (by linarith)
  have hUle : ∀ f : ℝ, 0 < f → ∀ H ∈ Set.Icc 0 f, U f ≤ Kf f H := by
    intro f hf H hH
    exact csInf_le (hKbdd f hf) (Set.mem_image_of_mem _ hH)
  have hKff : ∀ f : ℝ, 0 < f → Kf f f = 1 + f := by
    intro f hf
    unfold Kf
    have : f * (f + f) ≠ 0 := by positivity
    rw [div_eq_iff this]; ring
  have hUsig : U (1 - s0) = σ0 := by
    unfold U
    apply IsLeast.csInf_eq
    refine ⟨⟨s0, ⟨by linarith, by linarith⟩, ?_⟩, ?_⟩
    · have := p4 s0 (by linarith)
      simp at this
      linarith
    · rintro _ ⟨H, ⟨hH0, hH1⟩, rfl⟩
      have := p4 H hH0
      have : 0 ≤ (2 * (1 - s0) - 1) * (H - s0) ^ 2 / ((1 - s0) * ((1 - s0) + H)) := by
        apply div_nonneg
        · apply mul_nonneg (by linarith) (sq_nonneg _)
        · apply mul_nonneg (by linarith) (by linarith)
      linarith
  have hsmall : ∀ f : ℝ, 0 < f → f ≤ s0 → U f < σ0 := by
    intro f hf hfs
    have := hUle f hf f ⟨hf.le, le_refl f⟩
    rw [hKff f hf] at this
    linarith
  have hlarge : ∀ f : ℝ, 0 < f → s0 < f → U f ≤ σ0 - σ0 * (f - (1 - s0)) ^ 2 / (f * (f + s0)) := by
    intro f hf hfs
    have := hUle f hf s0 ⟨by linarith, hfs.le⟩
    have := p5 f hf
    linarith
  refine ⟨⟨by linarith, by linarith, hs0lo, hs0hi, by linear_combination (-1:ℝ) * hq0⟩,
    ⟨?_, by rw [hσ0]; ring⟩, ⟨?_, hσ0hi, hPσ0, ?_⟩, p4, p5, ⟨?_, ?_, ?_⟩⟩
  · unfold Hc
    rw [div_eq_iff (by linarith : (1:ℝ) - s0 ≠ 0), hσ0]
    linear_combination 2 * hq0
  · by_contra h
    push Not at h
    have hP : 0 < sigmaPoly (119/75) := by rw [hPdef]; norm_num
    rcases eq_or_lt_of_le h with h' | h'
    · rw [h'] at hPσ0; linarith
    · have := hPanti σ0 (119/75) (by linarith) h' (by norm_num); linarith
  · rintro s ⟨hs1, hs2⟩ hs
    rcases lt_trichotomy s σ0 with h | h | h
    · have := hPanti s σ0 hs1.le h hσ0hi.le; linarith
    · exact h
    · have := hPanti σ0 s (by linarith) h hs2.le; linarith
  · refine ⟨⟨1 - s0, ⟨by linarith, by linarith⟩, hUsig⟩, ?_⟩
    rintro _ ⟨f, ⟨hf0, hf1⟩, rfl⟩
    by_cases hfs : f ≤ s0
    · exact (hsmall f hf0 hfs).le
    · push Not at hfs
      have := hlarge f hf0 hfs
      have : 0 ≤ σ0 * (f - (1 - s0)) ^ 2 / (f * (f + s0)) := by
        apply div_nonneg
        · apply mul_nonneg (by linarith) (sq_nonneg _)
        · apply mul_nonneg (by linarith) (by linarith)
      linarith
  · rintro f ⟨hf0, hf1⟩ hU
    by_cases hfs : f ≤ s0
    · have := hsmall f hf0 hfs; linarith
    · push Not at hfs
      have h1 := hlarge f hf0 hfs
      by_contra hne
      have hsq : 0 < (f - (1 - s0)) ^ 2 := by
        have hne' : f - (1 - s0) ≠ 0 := sub_ne_zero.mpr hne
        exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne'))
      have : 0 < σ0 * (f - (1 - s0)) ^ 2 / (f * (f + s0)) :=
        div_pos (mul_pos (by linarith) hsq) (mul_pos hf0 (by linarith))
      linarith
  · refine ⟨⟨s0, ⟨by linarith, by linarith⟩, ?_⟩, ?_⟩
    · unfold Hc
      rw [div_eq_iff (by linarith : (1:ℝ) - s0 ≠ 0), hσ0]
      linear_combination 2 * hq0
    · rintro _ ⟨x, ⟨hx0, hx1⟩, rfl⟩
      unfold Hc
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 - x)]
      have key : σ0 * (1 - x) - (1 + x) * (1 - 2 * x ^ 2) = 2 * (x - s0) ^ 2 * (x + 1 + 2 * s0) := by
        rw [hσ0]; linear_combination (-2) * hq0
      nlinarith [mul_nonneg (sq_nonneg (x - s0)) (by linarith : (0:ℝ) ≤ x + 1 + 2 * s0)]

