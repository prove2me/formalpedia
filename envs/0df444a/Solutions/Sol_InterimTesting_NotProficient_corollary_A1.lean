-- Prove2me | solution 1 for InterimTesting.NotProficient.corollary_A1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:45:42.776577+00:00
-- url     : https://prove2.me/submissions/249ea6a3-5c0c-4205-bd15-296661edce81

import Mathlib
import Definitions.Def_InterimTesting_NotProficient_Model

namespace Aux_InterimW31
open InterimTesting.NotProficient

lemma den_pos {q a b : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (ha : 0 < a) (hb : 0 < b) :
    0 < q * a + (1 - q) * b := by
  rcases hq.eq_or_lt with h | h
  · rw [← h]; simp; exact hb
  · nlinarith [mul_pos h ha, mul_nonneg (sub_nonneg.2 hq1) hb.le]

lemma postP (θ : Params) (S0 : Prof) (e0 : ℝ) :
    post θ false S0 e0 .P = toP θ S0 e0 * θ.φPP /
      (toP θ S0 e0 * θ.φPP + (1 - toP θ S0 e0) * θ.φPN) := by
  simp [post, obsProb, joint, sig, acc]

lemma postN (θ : Params) (S0 : Prof) (e0 : ℝ) :
    post θ false S0 e0 .N = toP θ S0 e0 * (1 - θ.φPP) /
      (toP θ S0 e0 * (1 - θ.φPP) + (1 - toP θ S0 e0) * (1 - θ.φPN)) := by
  simp [post, obsProb, joint, sig, acc]

lemma toP_bounds (θ : Params) (hθ : θ.Standing) (S0 : Prof) (e : ℝ) (he : e ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ toP θ S0 e ∧ toP θ S0 e ≤ 1 := by
  obtain ⟨hA, hB, hAB, hμ0, hμ1, hN, hNP, hP1⟩ := hθ
  have h1 : 0 ≤ θ.A * e + θ.B := by nlinarith [he.1]
  have h2 : θ.A * e + θ.B ≤ 1 := by nlinarith [he.2]
  cases S0 <;> simp only [toP]
  · exact ⟨h1, h2⟩
  · constructor <;> nlinarith

lemma toP_mono (θ : Params) (hθ : θ.Standing) (S0 : Prof) {e e' : ℝ} (h : e ≤ e') :
    toP θ S0 e ≤ toP θ S0 e' := by
  obtain ⟨hA, hB, hAB, hμ0, hμ1, hN, hNP, hP1⟩ := hθ
  cases S0 <;> simp only [toP]
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_left h hA.le]

lemma T1p_anti (θ : Params) (hθ : θ.Standing) {p p' : ℝ} (h0 : 0 ≤ p) (h : p ≤ p') :
    T1p θ p' ≤ T1p θ p := by
  obtain ⟨hA, hB, hAB, hμ0, hμ1, hN, hNP, hP1⟩ := hθ
  unfold T1p
  apply one_div_le_one_div_of_le
  · apply mul_pos hA; nlinarith
  · apply mul_le_mul_of_nonneg_left _ hA.le; nlinarith

lemma f_nonneg {q a b : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (ha : 0 < a) (hb : 0 < b) :
    0 ≤ q * a / (q * a + (1 - q) * b) :=
  div_nonneg (mul_nonneg hq ha.le) (den_pos hq hq1 ha hb).le

lemma f_mono {q q' a b : ℝ} (hq : 0 ≤ q) (hq1 : q' ≤ 1) (ha : 0 < a) (hb : 0 < b)
    (h : q ≤ q') : q * a / (q * a + (1 - q) * b) ≤ q' * a / (q' * a + (1 - q') * b) := by
  rw [div_le_div_iff₀ (den_pos hq (h.trans hq1) ha hb) (den_pos (hq.trans h) hq1 ha hb)]
  nlinarith [mul_nonneg (mul_pos ha hb).le (sub_nonneg.2 h)]

end Aux_InterimW31

open InterimTesting.NotProficient Aux_InterimW31 in
theorem solution (θ : Params) (hθ : θ.Standing) (S0 : Prof) :
    (∀ e0 ∈ Set.Icc (0 : ℝ) 1, T1 θ false S0 e0 .P ≤ T1 θ false S0 e0 .N) ∧
      (∀ (x : Prof), ∀ e ∈ Set.Icc (0 : ℝ) 1, ∀ e' ∈ Set.Icc (0 : ℝ) 1, e ≤ e' →
        T1 θ false S0 e' x ≤ T1 θ false S0 e x) := by
  have hθ' := hθ
  obtain ⟨hA, hB, hAB, hμ0, hμ1, hN, hNP, hP1⟩ := hθ'
  have ha1 : 0 < θ.φPP := lt_of_lt_of_le hN hNP
  have ha2 : 0 < 1 - θ.φPP := by linarith
  have hb2 : 0 < 1 - θ.φPN := by linarith
  refine ⟨fun e0 he0 => ?_, fun x e he e' he' hle => ?_⟩
  · unfold T1
    obtain ⟨hq0, hq1⟩ := toP_bounds θ hθ S0 e0 he0
    set q := toP θ S0 e0
    apply T1p_anti θ hθ
    · rw [postN]; exact f_nonneg hq0 hq1 ha2 hb2
    · rw [postN, postP, div_le_div_iff₀ (den_pos hq0 hq1 ha2 hb2) (den_pos hq0 hq1 ha1 hN)]
      nlinarith [mul_nonneg (mul_nonneg hq0 (sub_nonneg.2 hq1)) (sub_nonneg.2 hNP)]
  · unfold T1
    obtain ⟨hq0, hq1⟩ := toP_bounds θ hθ S0 e he
    obtain ⟨hq0', hq1'⟩ := toP_bounds θ hθ S0 e' he'
    have hm := toP_mono θ hθ S0 hle
    apply T1p_anti θ hθ
    · cases x
      · rw [postP]; exact f_nonneg hq0 hq1 ha1 hN
      · rw [postN]; exact f_nonneg hq0 hq1 ha2 hb2
    · cases x
      · rw [postP, postP]; exact f_mono hq0 hq1' ha1 hN hm
      · rw [postN, postN]; exact f_mono hq0 hq1' ha2 hb2 hm
