-- Prove2me | solution 1 for MFIrrev.Equilibrium.roots_4_29
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T12:51:54.900152+00:00
-- url     : https://prove2.me/submissions/f1d675e2-425f-40d6-8508-de194f785d9a

import Mathlib
import Definitions.Def_MFIrrev_Equilibrium_Analytic

open MFIrrev.Equilibrium

/-- Pure real-variable version of the root structure of `ϕ̄`. -/
lemma mfirrev_roots_core (s0 s1 δ p0 p1 A0 A1 B0 B1 D am : ℝ) (hs0 : 0 < s0) (hs1 : 0 < s1)
    (hδ : 0 < δ) (hp0 : 0 < p0) (hp0' : p0 < 1) (hp1 : 0 < p1) (hp1' : p1 < 1)
    (hA0 : A0 = s0 / 2) (hA1 : A1 = s1 / 2) (hB0 : B0 = δ + s0 / 2) (hB1 : B1 = δ + s1 / 2)
    (hD : D = B0 ^ 2 + 2 * s0 * p0) (ham : am = (-B0 - Real.sqrt D) / s0) :
    ∃ θ1 θ2 θ4 : ℝ, θ1 < θ2 ∧ θ2 < 0 ∧ 0 < θ4 ∧
      (∀ θ : ℝ, (A0 * θ ^ 2 + B0 * θ - p0) * (A1 * θ ^ 2 + B1 * θ - p1)
          - p0 * p1 = 0 ↔ θ = θ1 ∨ θ = θ2 ∨ θ = 0 ∨ θ = θ4) ∧
      θ1 < am ∧ am < θ2 := by
  have hA0p : 0 < A0 := by rw [hA0]; positivity
  have hA1p : 0 < A1 := by rw [hA1]; positivity
  have hB0p : 0 < B0 := by rw [hB0]; positivity
  have hB1p : 0 < B1 := by rw [hB1]; positivity
  have hDnn : 0 ≤ D := by rw [hD]; positivity
  have hsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt hDnn
  have hsqB : B0 < Real.sqrt D := by
    rw [show B0 = Real.sqrt (B0 ^ 2) from (Real.sqrt_sq hB0p.le).symm]
    exact Real.sqrt_lt_sqrt (by positivity) (by rw [hD]; nlinarith [mul_pos hs0 hp0])
  obtain ⟨ap, hap⟩ : ∃ ap : ℝ, ap = (-B0 + Real.sqrt D) / s0 := ⟨_, rfl⟩
  have ham_neg : am < 0 := by rw [ham]; exact div_neg_of_neg_of_pos (by linarith) hs0
  have hap_pos : 0 < ap := by rw [hap]; exact div_pos (by linarith) hs0
  -- factorization of ϕ₁
  have hfac1 : ∀ θ, A0 * θ ^ 2 + B0 * θ - p0 = A0 * (θ - ap) * (θ - am) := by
    intro θ
    rw [ham, hap, hA0]
    field_simp
    have : Real.sqrt D ^ 2 = B0 ^ 2 + 2 * s0 * p0 := by rw [hsq, hD]
    linear_combination this
  -- the cubic g with ϕ̄ = θ g
  let g : ℝ → ℝ := fun θ => A0 * A1 * θ ^ 3 + (A0 * B1 + A1 * B0) * θ ^ 2
    + (B0 * B1 - A0 * p1 - A1 * p0) * θ - (B0 * p1 + B1 * p0)
  have hg : ∀ θ, (A0 * θ ^ 2 + B0 * θ - p0) * (A1 * θ ^ 2 + B1 * θ - p1) - p0 * p1 = θ * g θ := by
    intro θ; simp only [g]; ring
  have gcont : Continuous g := by simp only [g]; fun_prop
  -- values of g
  have hg_am : 0 < g am := by
    have h := hg am
    rw [hfac1 am] at h
    have h2 : am * g am = -(p0 * p1) := by rw [← h]; ring
    by_contra hc; push Not at hc
    have := mul_nonneg_of_nonpos_of_nonpos ham_neg.le hc
    linarith [mul_pos hp0 hp1]
  have hg_ap : g ap < 0 := by
    have h := hg ap
    rw [hfac1 ap] at h
    have h2 : ap * g ap = -(p0 * p1) := by rw [← h]; ring
    by_contra hc; push Not at hc
    have := mul_nonneg hap_pos.le hc
    linarith [mul_pos hp0 hp1]
  have hg0 : g 0 < 0 := by
    simp only [g]; nlinarith [mul_pos hB0p hp1, mul_pos hB1p hp0]
  -- a large point U
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = 1 + (2 * B0 + 6) / s0 + (2 * B1 + 6) / s1 := ⟨_, rfl⟩
  have hd0 := div_pos (by linarith : (0:ℝ) < 2 * B0 + 6) hs0
  have hd1 := div_pos (by linarith : (0:ℝ) < 2 * B1 + 6) hs1
  have hU1 : 1 ≤ U := by rw [hU]; linarith
  have hU0 : (2 * B0 + 6) / s0 ≤ U := by rw [hU]; linarith
  have hU1' : (2 * B1 + 6) / s1 ≤ U := by rw [hU]; linarith
  have hsU0 : 2 * B0 + 6 ≤ s0 * U := by
    have := (div_le_iff₀ hs0).1 hU0; linarith
  have hsU1 : 2 * B1 + 6 ≤ s1 * U := by
    have := (div_le_iff₀ hs1).1 hU1'; linarith
  have hq0 : (B0 + 3) * U ≤ A0 * U ^ 2 := by
    have := mul_le_mul_of_nonneg_right hsU0 (by linarith : (0:ℝ) ≤ U)
    rw [hA0]; nlinarith
  have hq1 : (B1 + 3) * U ≤ A1 * U ^ 2 := by
    have := mul_le_mul_of_nonneg_right hsU1 (by linarith : (0:ℝ) ≤ U)
    rw [hA1]; nlinarith
  have hBU0 : 0 ≤ B0 * U := mul_nonneg hB0p.le (by linarith)
  have hBU1 : 0 ≤ B1 * U := mul_nonneg hB1p.le (by linarith)
  have hφ0p : 2 * p0 ≤ A0 * U ^ 2 + B0 * U - p0 := by linarith
  have hφ1p : 2 * p1 ≤ A1 * U ^ 2 + B1 * U - p1 := by linarith
  have hφ0m : 2 * p0 ≤ A0 * (-U) ^ 2 + B0 * (-U) - p0 := by
    have : A0 * (-U) ^ 2 + B0 * (-U) - p0 = A0 * U ^ 2 - B0 * U - p0 := by ring
    rw [this]; linarith
  have hφ1m : 2 * p1 ≤ A1 * (-U) ^ 2 + B1 * (-U) - p1 := by
    have : A1 * (-U) ^ 2 + B1 * (-U) - p1 = A1 * U ^ 2 - B1 * U - p1 := by ring
    rw [this]; linarith
  have hpp := mul_pos hp0 hp1
  have hgU : 0 < g U := by
    have h := hg U
    have hm := mul_le_mul hφ0p hφ1p (by linarith) (by linarith)
    have hpos : 0 < (A0 * U ^ 2 + B0 * U - p0) * (A1 * U ^ 2 + B1 * U - p1) - p0 * p1 := by
      linarith
    rw [h] at hpos
    by_contra hc; push Not at hc
    have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ U) hc
    linarith
  have hgmU : g (-U) < 0 := by
    have h := hg (-U)
    have hm := mul_le_mul hφ0m hφ1m (by linarith) (by linarith)
    have hpos : 0 < (A0 * (-U) ^ 2 + B0 * (-U) - p0) * (A1 * (-U) ^ 2 + B1 * (-U) - p1)
        - p0 * p1 := by linarith
    rw [h] at hpos
    by_contra hc; push Not at hc
    have := mul_nonpos_of_nonpos_of_nonneg (by linarith : -U ≤ 0) hc
    linarith
  have hmU_am : -U < am := by
    have h := hfac1 (-U)
    by_contra hc; push Not at hc
    have : A0 * (-U - ap) * (-U - am) ≤ 0 := by
      have h1 : -U - ap < 0 := by linarith
      have h2 : 0 ≤ -U - am := by linarith
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hA0p.le h1.le) h2
    linarith
  have hap_U : ap < U := by
    have h := hfac1 U
    by_contra hc; push Not at hc
    have : A0 * (U - ap) * (U - am) ≤ 0 := by
      have h1 : U - ap ≤ 0 := by linarith
      have h2 : 0 < U - am := by linarith
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hA0p.le h1) h2.le
    linarith
  -- IVT
  obtain ⟨θ1, hθ1, hgθ1⟩ : ∃ θ ∈ Set.Ioo (-U) am, g θ = 0 :=
    intermediate_value_Ioo hmU_am.le gcont.continuousOn ⟨hgmU, hg_am⟩
  obtain ⟨θ2, hθ2, hgθ2⟩ : ∃ θ ∈ Set.Ioo am 0, g θ = 0 :=
    intermediate_value_Ioo' ham_neg.le gcont.continuousOn ⟨hg0, hg_am⟩
  obtain ⟨θ4, hθ4, hgθ4⟩ : ∃ θ ∈ Set.Ioo ap U, g θ = 0 :=
    intermediate_value_Ioo hap_U.le gcont.continuousOn ⟨hg_ap, hgU⟩
  refine ⟨θ1, θ2, θ4, by linarith [hθ1.2, hθ2.1], hθ2.2, by linarith [hθ4.1], ?_, hθ1.2, hθ2.1⟩
  have hc3 : A0 * A1 ≠ 0 := (mul_pos hA0p hA1p).ne'
  intro θ
  rw [hg θ]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h0 | hgθ
    · exact Or.inr (Or.inr (Or.inl h0))
    · by_contra hne
      push Not at hne
      obtain ⟨n1, n2, -, n4⟩ := hne
      have d12 : θ1 ≠ θ2 := by linarith [hθ1.2, hθ2.1]
      have d14 : θ1 ≠ θ4 := by linarith [hθ1.2, hθ2.1, hθ2.2, hθ4.1]
      have d24 : θ2 ≠ θ4 := by linarith [hθ2.2, hθ4.1]
      simp only [g] at hgθ hgθ1 hgθ2 hgθ4
      generalize A0 * A1 = c3 at hgθ hgθ1 hgθ2 hgθ4 hc3
      generalize A0 * B1 + A1 * B0 = c2 at hgθ hgθ1 hgθ2 hgθ4
      generalize B0 * B1 - A0 * p1 - A1 * p0 = c1 at hgθ hgθ1 hgθ2 hgθ4
      generalize B0 * p1 + B1 * p0 = c0 at hgθ hgθ1 hgθ2 hgθ4
      -- first divided differences
      have e1 : ∀ x y : ℝ, x ≠ y → c3 * x ^ 3 + c2 * x ^ 2 + c1 * x - c0 = 0 →
          c3 * y ^ 3 + c2 * y ^ 2 + c1 * y - c0 = 0 →
          c3 * (x ^ 2 + x * y + y ^ 2) + c2 * (x + y) + c1 = 0 := by
        intro x y hxy hx hy
        have : (x - y) * (c3 * (x ^ 2 + x * y + y ^ 2) + c2 * (x + y) + c1) = 0 := by
          linear_combination hx - hy
        rcases mul_eq_zero.1 this with h | h
        · exact absurd (sub_eq_zero.1 h) hxy
        · exact h
      have h12 := e1 θ θ1 n1 hgθ hgθ1
      have h22 := e1 θ θ2 n2 hgθ hgθ2
      have h42 := e1 θ θ4 n4 hgθ hgθ4
      have f1 : (θ1 - θ2) * (c3 * (θ + θ1 + θ2) + c2) = 0 := by linear_combination h12 - h22
      have f2 : (θ1 - θ4) * (c3 * (θ + θ1 + θ4) + c2) = 0 := by linear_combination h12 - h42
      have g1 := (mul_eq_zero.1 f1).resolve_left (sub_ne_zero.2 d12)
      have g2 := (mul_eq_zero.1 f2).resolve_left (sub_ne_zero.2 d14)
      have : c3 * (θ2 - θ4) = 0 := by linear_combination g1 - g2
      rcases mul_eq_zero.1 this with h | h
      · exact hc3 h
      · exact d24 (sub_eq_zero.1 h)
  · rintro (h | h | h | h) <;> subst h <;> simp [hgθ1, hgθ2, hgθ4]

theorem solution (m : Params) (hδ : 0 < m.δ) (hσ : ∀ j, 0 < m.σ j)
    (hp : ∀ j, 0 < m.p j ∧ m.p j < 1) :
    ∃ θ1 θ2 θ4 : ℝ, θ1 < θ2 ∧ θ2 < 0 ∧ 0 < θ4 ∧
      (∀ θ : ℝ, phiBar m θ = 0 ↔ θ = θ1 ∨ θ = θ2 ∨ θ = 0 ∨ θ = θ4) ∧
      θ1 < alphaMinus m ∧ alphaMinus m < θ2 :=
  mfirrev_roots_core (m.σ 0 ^ 2) (m.σ 1 ^ 2) m.δ (m.p 0) (m.p 1) _ _ _ _ _ _ (pow_pos (hσ 0) 2)
    (pow_pos (hσ 1) 2) hδ (hp 0).1 (hp 0).2 (hp 1).1 (hp 1).2 rfl rfl rfl rfl rfl rfl
