-- Prove2me | solution 1 for NewsBundling.Negotiated.lemma4_equilibrium_quality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T19:30:29.884054+00:00
-- url     : https://prove2.me/submissions/60a0891d-8365-4c56-955b-c522e4d6b0b0

import Mathlib
import Definitions.Def_NewsBundling_Negotiated_Setting
import Theorems.Thm_NewsBundling_Unilateral_lemma2_attention
import Theorems.Thm_NewsBundling_Unilateral_eq2_publisher_profit

open NewsBundling.Unilateral

/-- Maximisers of the piecewise publisher profit (2). -/
lemma nb5_opt (β φ0 φ1 c Λ : ℝ) (h : StandingAssumptions β φ0 φ1 c Λ) (P : ℝ → ℝ)
    (hP : ∀ q ∈ Set.Icc (0 : ℝ) 1, P q =
      if q ≤ Λ then φ1 * q - c * q ^ 2 / 2
      else φ1 * Λ * (1 - q) / (1 - Λ) + β * (q - Λ) / (1 - Λ) - c * q ^ 2 / 2) :
    (∀ Q ∈ Set.Icc (0 : ℝ) 1, (∀ q ∈ Set.Icc (0 : ℝ) 1, P q ≤ P Q) →
      (cdagger β φ1 Λ < c → Q = qL φ1 c) ∧ (c < cdagger β φ1 Λ → Q = qH β φ1 c Λ) ∧
      (c = cdagger β φ1 Λ → Q = qL φ1 c ∨ Q = qH β φ1 c Λ)) ∧
    (cdagger β φ1 Λ ≤ c → qL φ1 c ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ q ∈ Set.Icc (0 : ℝ) 1, P q ≤ P (qL φ1 c)) ∧
    (c ≤ cdagger β φ1 Λ → qH β φ1 c Λ ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ q ∈ Set.Icc (0 : ℝ) 1, P q ≤ P (qH β φ1 c Λ)) := by
  obtain ⟨_, ⟨hφ1, hφ1'⟩, hφβ, hc, hΛ0, hΛ1⟩ := h
  have hc0 : 0 < c := by linarith
  have hΛ' : 0 < 1 - Λ := by linarith
  set cd := cdagger β φ1 Λ with hcd
  set xL := qL φ1 c with hxL
  set xH := qH β φ1 c Λ with hxH
  set VL := φ1 ^ 2 / (2 * c) with hVL
  set D := (β - φ1) * Λ / (c * (1 - Λ)) * (c - cd) with hD
  have hK : 0 < (β - φ1) * Λ / (c * (1 - Λ)) := by
    apply div_pos (mul_pos (by linarith) hΛ0) (mul_pos hc0 hΛ')
  have I1 : ∀ q : ℝ, φ1 * q - c * q ^ 2 / 2 = VL - c / 2 * (q - xL) ^ 2 := by
    intro q; rw [hVL, hxL]; unfold qL; field_simp; ring
  have I2 : ∀ q : ℝ, φ1 * Λ * (1 - q) / (1 - Λ) + β * (q - Λ) / (1 - Λ) - c * q ^ 2 / 2 =
      VL - D - c / 2 * (q - xH) ^ 2 := by
    intro q; rw [hVL, hD, hxH, hcd]; unfold qH cdagger
    have : (1 - Λ) ≠ 0 := hΛ'.ne'
    have : Λ ≠ 0 := hΛ0.ne'
    field_simp; ring
  have hDsign : (0 < D ↔ cd < c) ∧ (D < 0 ↔ c < cd) ∧ (D = 0 ↔ c = cd) := by
    refine ⟨⟨fun h => ?_, fun h => mul_pos hK (by linarith)⟩,
      ⟨fun h => ?_, fun h => mul_neg_of_pos_of_neg hK (by linarith)⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
    · by_contra h'; push Not at h'
      exact absurd h (not_lt.2 (mul_nonpos_of_nonneg_of_nonpos hK.le (by linarith)))
    · by_contra h'; push Not at h'
      exact absurd h (not_lt.2 (mul_nonneg hK.le (by linarith)))
    · rcases mul_eq_zero.1 h with h1 | h1
      · exact absurd h1 hK.ne'
      · linarith
    · rw [hD, h]; ring
  -- c† > φ1/Λ
  have hcdL : φ1 < cd * Λ := by
    have : cd * (2 * Λ * (1 - Λ)) = β + φ1 * (1 - 2 * Λ) := by
      rw [hcd]; unfold cdagger; field_simp
    nlinarith [mul_pos hΛ0 hΛ']
  have hcdH : cd * (Λ * (1 - Λ)) < β - Λ * φ1 := by
    have : cd * (2 * Λ * (1 - Λ)) = β + φ1 * (1 - 2 * Λ) := by
      rw [hcd]; unfold cdagger; field_simp
    nlinarith
  have hxLmem : cd ≤ c → 0 ≤ xL ∧ xL ≤ Λ := by
    intro hle
    refine ⟨div_nonneg hφ1.le hc0.le, ?_⟩
    rw [hxL]; unfold qL; rw [div_le_iff₀ hc0]
    nlinarith
  have hxHmem : c ≤ cd → Λ < xH ∧ xH ≤ 1 := by
    intro hle
    rw [hxH]; unfold qH
    have hpos : 0 < c * (1 - Λ) := mul_pos hc0 hΛ'
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hpos]; nlinarith [mul_pos hΛ0 hΛ']
    · rw [div_le_one hpos]; nlinarith
  -- bounds
  have Plow : ∀ q ∈ Set.Icc (0 : ℝ) 1, q ≤ Λ → P q = VL - c / 2 * (q - xL) ^ 2 := by
    intro q hq hqΛ; rw [hP q hq, if_pos hqΛ, I1]
  have Phigh : ∀ q ∈ Set.Icc (0 : ℝ) 1, Λ < q → P q = VL - D - c / 2 * (q - xH) ^ 2 := by
    intro q hq hqΛ; rw [hP q hq, if_neg (not_le.2 hqΛ), I2]
  have sqpos : ∀ x y : ℝ, 0 ≤ c / 2 * (x - y) ^ 2 := fun x y =>
    mul_nonneg (by linarith) (sq_nonneg _)
  have sqzero : ∀ x y : ℝ, c / 2 * (x - y) ^ 2 ≤ 0 → x = y := by
    intro x y hxy
    have h0 : c / 2 * (x - y) ^ 2 = 0 := le_antisymm hxy (sqpos x y)
    rcases mul_eq_zero.1 h0 with h1 | h1
    · linarith
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1; linarith
  have Pbound : ∀ q ∈ Set.Icc (0 : ℝ) 1, P q ≤ VL ∧ P q ≤ VL - D ∨ True := fun _ _ => Or.inr trivial
  clear Pbound
  have PleL : ∀ q ∈ Set.Icc (0 : ℝ) 1, 0 ≤ D → P q ≤ VL := by
    intro q hq hD0
    rcases le_or_gt q Λ with hqΛ | hqΛ
    · rw [Plow q hq hqΛ]; linarith [sqpos q xL]
    · rw [Phigh q hq hqΛ]; linarith [sqpos q xH]
  have PleH : ∀ q ∈ Set.Icc (0 : ℝ) 1, D ≤ 0 → P q ≤ VL - D := by
    intro q hq hD0
    rcases le_or_gt q Λ with hqΛ | hqΛ
    · rw [Plow q hq hqΛ]; linarith [sqpos q xL]
    · rw [Phigh q hq hqΛ]; linarith [sqpos q xH]
  have xLmem : cd ≤ c → xL ∈ Set.Icc (0 : ℝ) 1 := fun hle =>
    ⟨(hxLmem hle).1, by linarith [(hxLmem hle).2]⟩
  have xHmem : c ≤ cd → xH ∈ Set.Icc (0 : ℝ) 1 := fun hle =>
    ⟨by linarith [(hxHmem hle).1], (hxHmem hle).2⟩
  have PxL : cd ≤ c → P xL = VL := by
    intro hle; rw [Plow xL (xLmem hle) (hxLmem hle).2]; simp
  have PxH : c ≤ cd → P xH = VL - D := by
    intro hle; rw [Phigh xH (xHmem hle) (hxHmem hle).1]; simp
  refine ⟨?_, ?_, ?_⟩
  · intro Q hQ hopt
    -- generic: Q is in one branch
    have caseL : Q ≤ Λ → cd ≤ c → Q = xL := by
      intro hQΛ hle
      have := hopt xL (xLmem hle)
      rw [PxL hle, Plow Q hQ hQΛ] at this
      exact sqzero Q xL (by linarith)
    have caseH : Λ < Q → c ≤ cd → Q = xH := by
      intro hQΛ hle
      have := hopt xH (xHmem hle)
      rw [PxH hle, Phigh Q hQ hQΛ] at this
      exact sqzero Q xH (by linarith)
    refine ⟨fun hlt => ?_, fun hlt => ?_, fun heq => ?_⟩
    · rcases le_or_gt Q Λ with hQΛ | hQΛ
      · exact caseL hQΛ hlt.le
      · exfalso
        have := hopt xL (xLmem hlt.le)
        rw [PxL hlt.le, Phigh Q hQ hQΛ] at this
        have := hDsign.1.2 hlt
        linarith [sqpos Q xH]
    · rcases le_or_gt Q Λ with hQΛ | hQΛ
      · exfalso
        have := hopt xH (xHmem hlt.le)
        rw [PxH hlt.le, Plow Q hQ hQΛ] at this
        have := hDsign.2.1.2 hlt
        linarith [sqpos Q xL]
      · exact caseH hQΛ hlt.le
    · rcases le_or_gt Q Λ with hQΛ | hQΛ
      · exact Or.inl (caseL hQΛ heq.ge)
      · exact Or.inr (caseH hQΛ heq.le)
  · intro hle
    refine ⟨xLmem hle, fun q hq => ?_⟩
    rw [PxL hle]
    exact PleL q hq (by
      rcases eq_or_lt_of_le hle with h1 | h1
      · exact (hDsign.2.2.2 h1.symm).ge
      · exact (hDsign.1.2 h1).le)
  · intro hle
    refine ⟨xHmem hle, fun q hq => ?_⟩
    rw [PxH hle]
    exact PleH q hq (by
      rcases eq_or_lt_of_le hle with h1 | h1
      · exact (hDsign.2.2.2 h1).le
      · exact (hDsign.2.1.2 h1).le)

/-- The candidate equilibrium profile with quality `Q`. -/
noncomputable def nb5Prof (Λ Q : ℝ) : Profile :=
  ⟨fun q lam => max ((q - lam) / (1 - lam)) 0, fun q => min q Λ, Q⟩

lemma nb5_T (q l : ℝ) (hl : l < 1) :
    1 - max ((q - l) / (1 - l)) 0 = if q ≤ l then 1 else (1 - q) / (1 - l) := by
  have hk : 0 < 1 - l := by linarith
  split_ifs with hql
  · rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg (by linarith) hk.le)]; ring
  · push Not at hql
    rw [max_eq_left (div_nonneg (by linarith) hk.le)]
    field_simp; ring

lemma nb5_prof_spe (β φ0 φ1 c Λ Q : ℝ) (h : StandingAssumptions β φ0 φ1 c Λ) :
    (∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ lam ∈ Set.Icc (0 : ℝ) Λ,
      IsConsumerBR q lam ((nb5Prof Λ Q).consumer q lam)) ∧
    (∀ q ∈ Set.Icc (0 : ℝ) 1,
      (nb5Prof Λ Q).platform q ∈ Set.Icc (0 : ℝ) Λ ∧
        ∀ lam ∈ Set.Icc (0 : ℝ) Λ,
          platformRevenue φ0 lam ((nb5Prof Λ Q).consumer q lam) ≤
            platformRevenue φ0 ((nb5Prof Λ Q).platform q)
              ((nb5Prof Λ Q).consumer q ((nb5Prof Λ Q).platform q))) ∧
    (∀ q ∈ Set.Icc (0 : ℝ) 1, publisherProfit β φ1 c (nb5Prof Λ Q) q =
      if q ≤ Λ then φ1 * q - c * q ^ 2 / 2
      else φ1 * Λ * (1 - q) / (1 - Λ) + β * (q - Λ) / (1 - Λ) - c * q ^ 2 / 2) := by
  obtain ⟨⟨hφ0, hφ0'⟩, ⟨hφ1, hφ1'⟩, hφβ, hc, hΛ0, hΛ1⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro q hq lam hlam
    exact (lemma2_attention q hq lam hlam.1 (by linarith [hlam.2]) _).2 rfl
  · intro q hq
    refine ⟨⟨le_min hq.1 hΛ0.le, min_le_right _ _⟩, ?_⟩
    intro lam hlam
    unfold platformRevenue nb5Prof
    simp only
    have hl1 : lam < 1 := by linarith [hlam.2]
    have hm1 : min q Λ < 1 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    rw [nb5_T q lam hl1, nb5_T q (min q Λ) hm1]
    have hk : 0 < 1 - lam := by linarith
    rcases le_or_gt q Λ with hqΛ | hqΛ
    · rw [min_eq_left hqΛ, if_pos le_rfl]
      split_ifs with hql
      · nlinarith [hlam.1]
      · push Not at hql
        rw [mul_div_assoc', div_le_iff₀ hk]
        nlinarith [mul_nonneg hφ0.le (by linarith : (0:ℝ) ≤ q - lam)]
    · rw [min_eq_right hqΛ.le, if_neg (not_le.2 hqΛ), if_neg (by linarith [hlam.2])]
      have hkΛ : 0 < 1 - Λ := by linarith
      rw [mul_div_assoc', mul_div_assoc', div_le_div_iff₀ hk hkΛ]
      have : 0 ≤ (1 - q) * (φ0 * (Λ - lam)) :=
        mul_nonneg (by linarith [hq.2]) (mul_nonneg hφ0.le (by linarith [hlam.2]))
      nlinarith
  · intro q hq
    unfold publisherProfit publisherRevenue nb5Prof
    simp only
    have hkΛ : 0 < 1 - Λ := by linarith
    split_ifs with hqΛ
    · rw [min_eq_left hqΛ, sub_self, zero_div, max_self]; ring
    · push Not at hqΛ
      rw [min_eq_right hqΛ.le, max_eq_left (div_nonneg (by linarith) hkΛ.le)]
      field_simp; ring

theorem solution (β φ0 φ1 c Λ : ℝ)
    (h : NewsBundling.Unilateral.StandingAssumptions β φ0 φ1 c Λ) :
    (∃ σ, NewsBundling.Unilateral.IsSPE β φ0 φ1 c Λ σ) ∧
      (∀ σ, NewsBundling.Unilateral.IsSPE β φ0 φ1 c Λ σ →
        (NewsBundling.Unilateral.cdagger β φ1 Λ < c → σ.quality = NewsBundling.Unilateral.qL φ1 c) ∧
          (c < NewsBundling.Unilateral.cdagger β φ1 Λ → σ.quality = NewsBundling.Unilateral.qH β φ1 c Λ) ∧
          (c = NewsBundling.Unilateral.cdagger β φ1 Λ → σ.quality = NewsBundling.Unilateral.qL φ1 c ∨ σ.quality = NewsBundling.Unilateral.qH β φ1 c Λ)) ∧
      (c = NewsBundling.Unilateral.cdagger β φ1 Λ →
        (∃ σ, NewsBundling.Unilateral.IsSPE β φ0 φ1 c Λ σ ∧ σ.quality = NewsBundling.Unilateral.qL φ1 c) ∧
          ∃ σ, NewsBundling.Unilateral.IsSPE β φ0 φ1 c Λ σ ∧ σ.quality = NewsBundling.Unilateral.qH β φ1 c Λ) := by
  -- the profit of the candidate profile does not depend on its quality
  have hPQ : ∀ Q, (nb5Prof Λ Q) = { nb5Prof Λ 0 with quality := Q } := fun Q => rfl
  have hprof : ∀ Q q, publisherProfit β φ1 c (nb5Prof Λ Q) q =
      publisherProfit β φ1 c (nb5Prof Λ 0) q := fun _ _ => rfl
  have O := nb5_opt β φ0 φ1 c Λ h (publisherProfit β φ1 c (nb5Prof Λ 0))
    (nb5_prof_spe β φ0 φ1 c Λ 0 h).2.2
  have mk : ∀ Q ∈ Set.Icc (0 : ℝ) 1,
      (∀ q ∈ Set.Icc (0 : ℝ) 1, publisherProfit β φ1 c (nb5Prof Λ 0) q ≤
        publisherProfit β φ1 c (nb5Prof Λ 0) Q) → IsSPE β φ0 φ1 c Λ (nb5Prof Λ Q) := by
    intro Q hQ hopt
    obtain ⟨h1, h2, _⟩ := nb5_prof_spe β φ0 φ1 c Λ Q h
    exact ⟨h1, h2, hQ, fun q hq => by rw [hprof, hprof]; exact hopt q hq⟩
  have exL : cdagger β φ1 Λ ≤ c → ∃ σ, IsSPE β φ0 φ1 c Λ σ ∧ σ.quality = qL φ1 c := by
    intro hle
    exact ⟨nb5Prof Λ (qL φ1 c), mk _ (O.2.1 hle).1 (O.2.1 hle).2, rfl⟩
  have exH : c ≤ cdagger β φ1 Λ → ∃ σ, IsSPE β φ0 φ1 c Λ σ ∧ σ.quality = qH β φ1 c Λ := by
    intro hle
    exact ⟨nb5Prof Λ (qH β φ1 c Λ), mk _ (O.2.2 hle).1 (O.2.2 hle).2, rfl⟩
  refine ⟨?_, ?_, fun heq => ⟨exL heq.ge, exH heq.le⟩⟩
  · rcases le_total (cdagger β φ1 Λ) c with hle | hle
    · obtain ⟨σ, hσ, _⟩ := exL hle; exact ⟨σ, hσ⟩
    · obtain ⟨σ, hσ, _⟩ := exH hle; exact ⟨σ, hσ⟩
  · intro σ hσ
    have O' := nb5_opt β φ0 φ1 c Λ h (publisherProfit β φ1 c σ)
      (eq2_publisher_profit β φ0 φ1 c Λ h σ hσ)
    exact O'.1 σ.quality hσ.2.2.1 hσ.2.2.2
