-- Prove2me | solution 1 for GilesMLMC.Complexity.case_a_complexity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:42:47.171989+00:00
-- url     : https://prove2.me/submissions/f9161d93-b3bc-4b6c-ab55-6f894d35b0bd

import Mathlib
import Definitions.Def_GilesMLMC_Complexity_Setup
import Definitions.Def_GilesMLMC_Complexity_Choices

set_option autoImplicit false
open GilesMLMC.Complexity

lemma gmc_eq7
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (α c₁ ε : ℝ) (hα : 1 / 2 ≤ α) (hc₁ : 0 < c₁) (hε : 0 < ε) (hε1 : ε < Real.exp (-1))
    (L : ℕ) (hL : (L : ℤ) = Lchoice M T α c₁ ε) :
    ∑ l ∈ Finset.range (L + 1), (h M T l)⁻¹ <
      (M : ℝ) ^ 2 / ((M : ℝ) - 1) * (Real.sqrt 2 * c₁) ^ (1 / α) * ε ^ (-2 : ℝ) := by
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) < M := by linarith
  have hMpos : (0 : ℝ) < M := by linarith
  have hαpos : 0 < α := by linarith
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos hM1
  have hε1' : ε < 1 := by
    have : Real.exp (-1) < Real.exp 0 := Real.exp_lt_exp.mpr (by norm_num)
    rw [Real.exp_zero] at this
    linarith
  set B : ℝ := (Real.sqrt 2 * c₁) ^ (1 / α) with hB
  have hBpos : 0 < B := by
    rw [hB]
    apply Real.rpow_pos_of_pos
    exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) hc₁
  set A : ℝ := Real.sqrt 2 * c₁ * T ^ α * ε⁻¹ with hA
  have hApos : 0 < A := by
    rw [hA]
    have := Real.rpow_pos_of_pos hT α
    positivity
  set x : ℝ := Real.log A / (α * Real.log (M : ℝ)) with hx
  have hLx : (L : ℝ) < x + 1 := by
    have h1 : ((L : ℤ) : ℝ) = (Lchoice M T α c₁ ε : ℝ) := by rw [hL]
    have h2 : (Lchoice M T α c₁ ε : ℝ) < x + 1 := by
      have := Int.ceil_lt_add_one x
      simpa [Lchoice, hx, hA] using this
    simpa using h1.trans_lt h2
  -- M^x = A^(1/α)
  have hMx : (M : ℝ) ^ x = A ^ (1 / α) := by
    rw [Real.rpow_def_of_pos hMpos, Real.rpow_def_of_pos hApos]
    congr 1
    rw [hx]
    field_simp
  have hAexp : A ^ (1 / α) = B * T * (ε ^ (1 / α))⁻¹ := by
    rw [hA, hB]
    rw [Real.mul_rpow (by positivity) (inv_nonneg.mpr hε.le),
      Real.mul_rpow (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hc₁).le
        (Real.rpow_nonneg hT.le _),
      ← Real.rpow_mul hT.le, Real.inv_rpow hε.le]
    rw [mul_one_div_cancel hαpos.ne', Real.rpow_one]
  have hεpow : (ε ^ (1 / α))⁻¹ ≤ ε ^ (-2 : ℝ) := by
    have h1 : ε ^ (2 : ℝ) ≤ ε ^ (1 / α) :=
      Real.rpow_le_rpow_of_exponent_ge hε hε1'.le (by
        rw [div_le_iff₀ hαpos]; linarith)
    have h2 : ε ^ (-2 : ℝ) = (ε ^ (2 : ℝ))⁻¹ := Real.rpow_neg hε.le 2
    rw [h2]
    exact inv_anti₀ (Real.rpow_pos_of_pos hε _) h1
  have key : (M : ℝ) ^ (L + 1) < (M : ℝ) ^ 2 * (B * T * ε ^ (-2 : ℝ)) := by
    have h1 : (M : ℝ) ^ ((L : ℝ) + 1) < (M : ℝ) ^ (x + 2) :=
      Real.rpow_lt_rpow_of_exponent_lt hM1 (by linarith)
    have h2 : (M : ℝ) ^ ((L : ℝ) + 1) = (M : ℝ) ^ (L + 1) := by
      rw [← Real.rpow_natCast]; norm_num
    have h3 : (M : ℝ) ^ (x + 2) = (M : ℝ) ^ x * (M : ℝ) ^ 2 := by
      rw [Real.rpow_add hMpos]; norm_num
    rw [h2, h3, hMx, hAexp] at h1
    have h4 : B * T * (ε ^ (1 / α))⁻¹ ≤ B * T * ε ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_left hεpow (by positivity)
    have h5 : (M : ℝ) ^ 2 * (B * T * (ε ^ (1 / α))⁻¹) ≤ (M : ℝ) ^ 2 * (B * T * ε ^ (-2 : ℝ)) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    nlinarith
  have hsum : ∑ l ∈ Finset.range (L + 1), (h M T l)⁻¹ =
      (∑ l ∈ Finset.range (L + 1), (M : ℝ) ^ l) / T := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l _
    simp [h, inv_div]
  have hgeom := geom_sum_mul (M : ℝ) (L + 1)
  have hMsub : 0 < (M : ℝ) - 1 := by linarith
  rw [hsum, div_lt_iff₀ hT]
  have h6 : (∑ l ∈ Finset.range (L + 1), (M : ℝ) ^ l) * ((M : ℝ) - 1) <
      (M : ℝ) ^ 2 * (B * T * ε ^ (-2 : ℝ)) := by
    rw [hgeom]; linarith
  have h7 : ∑ l ∈ Finset.range (L + 1), (M : ℝ) ^ l <
      (M : ℝ) ^ 2 * (B * T * ε ^ (-2 : ℝ)) / ((M : ℝ) - 1) := by
    rw [lt_div_iff₀ hMsub]; exact h6
  have h8 : (M : ℝ) ^ 2 / ((M : ℝ) - 1) * B * ε ^ (-2 : ℝ) * T =
      (M : ℝ) ^ 2 * (B * T * ε ^ (-2 : ℝ)) / ((M : ℝ) - 1) := by
    field_simp
  rw [h8]; exact h7

lemma gmc_Lbound
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (α c₁ ε : ℝ) (hα : 1 / 2 ≤ α) (hc₁ : 0 < c₁) (hε : 0 < ε) (hε1 : ε < Real.exp (-1))
    (L : ℕ) (hL : (L : ℤ) = Lchoice M T α c₁ ε) :
    (L : ℝ) + 1 ≤ c₅ M T α c₁ * (-Real.log ε) ∧ 1 < -Real.log ε := by
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) < M := by linarith
  have hαpos : 0 < α := by linarith
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos hM1
  have hℓ : 1 < -Real.log ε := by
    have h1 : Real.log ε < Real.log (Real.exp (-1)) := Real.log_lt_log hε hε1
    rw [Real.log_exp] at h1
    linarith
  refine ⟨?_, hℓ⟩
  set u : ℝ := Real.log (Real.sqrt 2 * c₁ * T ^ α) with hu
  set q : ℝ := 1 / (α * Real.log (M : ℝ)) with hq
  have hqpos : 0 < q := by rw [hq]; positivity
  have hApos : 0 < Real.sqrt 2 * c₁ * T ^ α := by
    have := Real.rpow_pos_of_pos hT α
    have : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  have hLx : (L : ℝ) < (u + (-Real.log ε)) * q + 1 := by
    have h1 : ((L : ℤ) : ℝ) = (Lchoice M T α c₁ ε : ℝ) := by rw [hL]
    have h2 : (Lchoice M T α c₁ ε : ℝ) <
        Real.log (Real.sqrt 2 * c₁ * T ^ α * ε⁻¹) / (α * Real.log (M : ℝ)) + 1 := by
      have := Int.ceil_lt_add_one (Real.log (Real.sqrt 2 * c₁ * T ^ α * ε⁻¹) /
        (α * Real.log (M : ℝ)))
      simpa [Lchoice] using this
    have h3 : Real.log (Real.sqrt 2 * c₁ * T ^ α * ε⁻¹) / (α * Real.log (M : ℝ)) =
        (u + (-Real.log ε)) * q := by
      rw [Real.log_mul hApos.ne' (inv_ne_zero hε.ne'), Real.log_inv, hq, hu]
      ring
    have h4 : (L : ℝ) = ((L : ℤ) : ℝ) := by simp
    rw [h4, h1]
    linarith
  have hmax : u * q ≤ max 0 (u / (α * Real.log (M : ℝ))) := by
    have : u / (α * Real.log (M : ℝ)) = u * q := by rw [hq]; ring
    rw [this]; exact le_max_right _ _
  have hm0 : 0 ≤ max 0 (u / (α * Real.log (M : ℝ))) := le_max_left _ _
  unfold c₅
  have hc : 1 / (α * Real.log (M : ℝ)) = q := rfl
  rw [hc]
  nlinarith [mul_nonneg (add_nonneg hm0 (by norm_num : (0:ℝ) ≤ 2)) (sub_nonneg.mpr hℓ.le),
    mul_nonneg hqpos.le (sub_nonneg.mpr hℓ.le)]

theorem solution
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (α c₁ c₂ c₃ : ℝ) (hα : 1 / 2 ≤ α) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (cost : ℕ → ℕ → ℝ) (h_iv : ∀ l N, 1 ≤ N → cost l N ≤ c₃ * N * (h M T l)⁻¹)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < Real.exp (-1))
    (L : ℕ) (hL : (L : ℤ) = Lchoice M T α c₁ ε) :
    totalCost cost (NA M T c₂ ε L) L ≤ c₄A M T α c₁ c₂ c₃ * ε ^ (-2 : ℝ) * Real.log ε ^ 2 := by
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) < M := by linarith
  have hMpos : (0 : ℝ) < M := by linarith
  have hMsub : 0 < (M : ℝ) - 1 := by linarith
  have hh : ∀ l, 0 < h M T l := by
    intro l; unfold h; positivity
  have hR : 0 < ε ^ (-2 : ℝ) := Real.rpow_pos_of_pos hε _
  obtain ⟨hLb, hℓ⟩ := gmc_Lbound M hM T hT α c₁ ε hα hc₁ hε hε1 L hL
  have h7 := gmc_eq7 M hM T hT α c₁ ε hα hc₁ hε hε1 L hL
  set R : ℝ := ε ^ (-2 : ℝ) with hRdef
  set B : ℝ := (Real.sqrt 2 * c₁) ^ (1 / α) with hB
  have hBpos : 0 < B := by
    rw [hB]
    apply Real.rpow_pos_of_pos
    exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) hc₁
  set P : ℝ := (L : ℝ) + 1 with hP
  have hPpos : 0 < P := by rw [hP]; positivity
  have harg : ∀ l, 0 < 2 * R * P * c₂ * h M T l := by
    intro l; have := hh l; positivity
  have hN1 : ∀ l, 1 ≤ NA M T c₂ ε L l := fun l => Nat.one_le_ceil_iff.mpr (harg l)
  have hNle : ∀ l, (NA M T c₂ ε L l : ℝ) ≤ 2 * R * P * c₂ * h M T l + 1 := fun l =>
    (Nat.ceil_lt_add_one (harg l).le).le
  have S1 : totalCost cost (NA M T c₂ ε L) L ≤
      ∑ l ∈ Finset.range (L + 1), c₃ * (2 * R * P * c₂ + (h M T l)⁻¹) := by
    unfold totalCost
    apply Finset.sum_le_sum
    intro l _
    refine (h_iv l _ (hN1 l)).trans ?_
    have hhl := hh l
    calc c₃ * (NA M T c₂ ε L l : ℝ) * (h M T l)⁻¹
        ≤ c₃ * (2 * R * P * c₂ * h M T l + 1) * (h M T l)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hhl.le)
          exact mul_le_mul_of_nonneg_left (hNle l) hc₃.le
      _ = c₃ * (2 * R * P * c₂ + (h M T l)⁻¹) := by
          field_simp
  have S2 : ∑ l ∈ Finset.range (L + 1), c₃ * (2 * R * P * c₂ + (h M T l)⁻¹) =
      c₃ * (P * (2 * R * P * c₂)) + c₃ * ∑ l ∈ Finset.range (L + 1), (h M T l)⁻¹ := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    simp only [hP]
    push_cast
    ring
  have hP2 : P ^ 2 ≤ (c₅ M T α c₁ * (-Real.log ε)) ^ 2 :=
    pow_le_pow_left₀ hPpos.le hLb 2
  have hℓ2 : 1 ≤ (-Real.log ε) ^ 2 := by nlinarith
  have hlogsq : Real.log ε ^ 2 = (-Real.log ε) ^ 2 := by ring
  have hX : 0 ≤ (M : ℝ) ^ 2 / ((M : ℝ) - 1) * B * R := by positivity
  unfold c₄A
  rw [hlogsq]
  calc totalCost cost (NA M T c₂ ε L) L
      ≤ c₃ * (P * (2 * R * P * c₂)) + c₃ * ∑ l ∈ Finset.range (L + 1), (h M T l)⁻¹ := by
        rw [← S2]; exact S1
    _ ≤ c₃ * (2 * R * c₂ * (c₅ M T α c₁ * (-Real.log ε)) ^ 2) +
          c₃ * ((M : ℝ) ^ 2 / ((M : ℝ) - 1) * B * R) := by
        have h1 : P * (2 * R * P * c₂) = 2 * R * c₂ * P ^ 2 := by ring
        rw [h1]
        have h2 : 2 * R * c₂ * P ^ 2 ≤ 2 * R * c₂ * (c₅ M T α c₁ * (-Real.log ε)) ^ 2 :=
          mul_le_mul_of_nonneg_left hP2 (by positivity)
        have h3 := mul_le_mul_of_nonneg_left h2 hc₃.le
        have h4 := mul_le_mul_of_nonneg_left h7.le hc₃.le
        linarith
    _ ≤ (2 * c₃ * c₅ M T α c₁ ^ 2 * c₂ +
          c₃ * ((M : ℝ) ^ 2 / ((M : ℝ) - 1)) * (Real.sqrt 2 * c₁) ^ (1 / α)) * R *
          (-Real.log ε) ^ 2 := by
        rw [← hB]
        have h5 : c₃ * ((M : ℝ) ^ 2 / ((M : ℝ) - 1) * B * R) ≤
            c₃ * ((M : ℝ) ^ 2 / ((M : ℝ) - 1) * B * R) * (-Real.log ε) ^ 2 := by
          have := mul_nonneg hc₃.le hX
          nlinarith
        have h6 : c₃ * (2 * R * c₂ * (c₅ M T α c₁ * (-Real.log ε)) ^ 2) =
            2 * c₃ * c₅ M T α c₁ ^ 2 * c₂ * R * (-Real.log ε) ^ 2 := by ring
        nlinarith [h5, h6]
