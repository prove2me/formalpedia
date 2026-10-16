-- Prove2me | solution 1 for JRPHard.RangeDiv.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-15T17:39:01.012243+00:00
-- url     : https://prove2.me/submissions/5f59cd90-14d5-4bb8-8648-4268c02fed1d

import Definitions.Def_JRPHard_RangeDiv_Setting
namespace JRPHard.RangeDiv

/-- integer key fact: for `q ≠ M`, `(M+1)(q-M)^2 ≥ q`. -/
lemma jrp3_int_fact (M q : ℕ) (hne : q ≠ M) :
    ((q : ℝ)) ≤ ((M : ℝ) + 1) * ((q : ℝ) - M) ^ 2 := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have h' : (q : ℝ) + 1 ≤ M := by exact_mod_cast h
    have hq : (0 : ℝ) ≤ q := by positivity
    have h1 : (1 : ℝ) ≤ ((q : ℝ) - M) ^ 2 := by nlinarith
    have h2 : ((M : ℝ) + 1) * 1 ≤ ((M : ℝ) + 1) * ((q : ℝ) - M) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    linarith
  · have h' : (M : ℝ) + 1 ≤ q := by exact_mod_cast h
    have hM : (0 : ℝ) ≤ M := by positivity
    have h1 : (1 : ℝ) ≤ ((q : ℝ) - M) ^ 2 := by nlinarith
    have h3 : ((q : ℝ) - M) ≤ ((q : ℝ) - M) ^ 2 := by nlinarith
    have h2 : (M : ℝ) * 1 ≤ (M : ℝ) * ((q : ℝ) - M) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 hM
    nlinarith

lemma jrp3_cost (M L U q₁ q₂ : ℕ) :
    rangeCost M L U q₁ q₂ =
      (q₁ : ℝ) + ((M : ℝ) ^ 3 * ((M : ℝ) + 1) / (q₂ : ℝ)
        + (M : ℝ) * ((M : ℝ) + 1) * (q₂ : ℝ)) + ((L : ℝ) * U) / (Nat.gcd q₁ q₂ : ℝ) := by
  simp [rangeCost, JRPHard.Periodic.periodicCost, JRPHard.Aperiodic.eoq, coefK0,
    JRPHard.Periodic.coefK2, JRPHard.Periodic.coefH2]

theorem lemma_3 (M L U : ℕ) (hI : IsRangeDivisorInstance M L U) :
    (coefK0 L U ≤ 2 * M ^ 4 ∧ JRPHard.Periodic.coefK2 M ≤ 2 * M ^ 4 ∧ JRPHard.Periodic.coefH2 M ≤ 2 * M ^ 4) ∧
    (HasDivisorIn M L U ↔
      ∃ q₁ q₂ : ℕ, 0 < q₁ ∧ 0 < q₂ ∧ rangeCost M L U q₁ q₂ ≤ threshold M L U) := by
  obtain ⟨hL, hLU, hUM, -⟩ := hI
  have hM : 0 < M := by omega
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · unfold coefK0
    have h1 : L * U ≤ M * M := Nat.mul_le_mul (by omega) hUM
    have h2 : M * M ≤ 2 * M ^ 4 := by
      have : M * M ≤ M ^ 4 := by
        calc M * M = M ^ 2 * 1 := by ring
          _ ≤ M ^ 2 * M ^ 2 := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega))
          _ = M ^ 4 := by ring
      omega
    omega
  · unfold JRPHard.Periodic.coefK2
    have : M ^ 3 * (M + 1) = M ^ 4 + M ^ 3 := by ring
    have h3 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right hM (by norm_num)
    omega
  · unfold JRPHard.Periodic.coefH2
    have : M * (M + 1) = M ^ 2 + M := by ring
    have h3 : M ^ 2 ≤ M ^ 4 := Nat.pow_le_pow_right hM (by norm_num)
    have h4 : M ≤ M ^ 4 := by
      calc M = M ^ 1 := by ring
        _ ≤ M ^ 4 := Nat.pow_le_pow_right hM (by norm_num)
    omega
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hLUr : (L : ℝ) ≤ U := by exact_mod_cast hLU
  have hUMr : (U : ℝ) ≤ M := by exact_mod_cast hUM
  constructor
  · rintro ⟨q, hqM, hLq, hqU⟩
    have hq : 0 < q := by omega
    refine ⟨q, M, hq, hM, ?_⟩
    rw [jrp3_cost, Nat.gcd_eq_left hqM]
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq
    have hLqr : (L : ℝ) ≤ q := by exact_mod_cast hLq
    have hqUr : (q : ℝ) ≤ U := by exact_mod_cast hqU
    have e1 : (M : ℝ) ^ 3 * ((M : ℝ) + 1) / (M : ℝ) = (M : ℝ) ^ 2 * ((M : ℝ) + 1) := by
      field_simp
    have e2 : ((L : ℝ) * U) / (q : ℝ) ≤ L + U - q := by
      rw [div_le_iff₀ hqr]
      nlinarith
    rw [e1]
    simp only [threshold]
    push_cast
    nlinarith
  · rintro ⟨q₁, q₂, hq₁, hq₂, h⟩
    rw [jrp3_cost] at h
    simp only [threshold] at h
    push_cast at h
    set g := Nat.gcd q₁ q₂ with hgdef
    have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hq₁
    have hgq : g ≤ q₁ := Nat.le_of_dvd hq₁ (Nat.gcd_dvd_left _ _)
    have hgr : (0 : ℝ) < g := by exact_mod_cast hg
    have hgqr : (g : ℝ) ≤ q₁ := by exact_mod_cast hgq
    have hq₂r : (0 : ℝ) < q₂ := by exact_mod_cast hq₂
    -- EOQ lower bound
    have hE : (M : ℝ) ^ 3 * ((M : ℝ) + 1) / (q₂ : ℝ) + (M : ℝ) * ((M : ℝ) + 1) * (q₂ : ℝ)
        = 2 * (M : ℝ) ^ 2 * ((M : ℝ) + 1)
          + (M : ℝ) * ((M : ℝ) + 1) * ((q₂ : ℝ) - M) ^ 2 / q₂ := by
      field_simp
      ring
    rw [hE] at h
    set D := (M : ℝ) * ((M : ℝ) + 1) * ((q₂ : ℝ) - M) ^ 2 / q₂ with hD
    have hD0 : 0 ≤ D := by positivity
    set X := ((L : ℝ) * U) / (g : ℝ) with hX
    have hXg : X * g = (L : ℝ) * U := by
      rw [hX]; field_simp
    by_cases hq2M : q₂ = M
    · subst hq2M
      have hgM : g ∣ q₂ := Nat.gcd_dvd_right _ _
      refine ⟨g, hgM, ?_, ?_⟩
      · by_contra hc
        push Not at hc
        have hc' : (g : ℝ) + 1 ≤ L := by exact_mod_cast hc
        have : X * g ≤ ((L : ℝ) + U - g) * g := by
          apply mul_le_mul_of_nonneg_right _ hgr.le
          linarith
        nlinarith
      · by_contra hc
        push Not at hc
        have hc' : (U : ℝ) + 1 ≤ g := by exact_mod_cast hc
        have : X * g ≤ ((L : ℝ) + U - g) * g := by
          apply mul_le_mul_of_nonneg_right _ hgr.le
          linarith
        nlinarith
    · exfalso
      have hDM : (M : ℝ) ≤ D := by
        rw [hD, le_div_iff₀ hq₂r]
        have := jrp3_int_fact M q₂ hq2M
        have h0 : (0 : ℝ) ≤ M := hMr.le
        nlinarith
      have : X * g ≤ ((L : ℝ) + U - M - g) * g := by
        apply mul_le_mul_of_nonneg_right _ hgr.le
        linarith
      by_cases hgL : (L : ℝ) ≤ g
      · nlinarith
      · push Not at hgL
        nlinarith

end JRPHard.RangeDiv


-- Platform entry point: restates the target verbatim.
namespace JRPHard.RangeDiv

theorem _root_.solution (M L U : ℕ) (hI : IsRangeDivisorInstance M L U) :
    (coefK0 L U ≤ 2 * M ^ 4 ∧ JRPHard.Periodic.coefK2 M ≤ 2 * M ^ 4 ∧ JRPHard.Periodic.coefH2 M ≤ 2 * M ^ 4) ∧
    (HasDivisorIn M L U ↔
      ∃ q₁ q₂ : ℕ, 0 < q₁ ∧ 0 < q₂ ∧ rangeCost M L U q₁ q₂ ≤ threshold M L U) := by
  apply @JRPHard.RangeDiv.lemma_3 <;> assumption

end JRPHard.RangeDiv
