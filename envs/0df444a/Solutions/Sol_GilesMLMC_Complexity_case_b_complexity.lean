-- Prove2me | solution 1 for GilesMLMC.Complexity.case_b_complexity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:53:10.277384+00:00
-- url     : https://prove2.me/submissions/cd9d1c21-a662-47d0-a2a8-7fe2077c3748

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

theorem solution
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (α β c₁ c₂ c₃ : ℝ) (hα : 1 / 2 ≤ α) (hβ : 1 < β)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (cost : ℕ → ℕ → ℝ) (h_iv : ∀ l N, 1 ≤ N → cost l N ≤ c₃ * N * (h M T l)⁻¹)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < Real.exp (-1))
    (L : ℕ) (hL : (L : ℤ) = Lchoice M T α c₁ ε) :
    totalCost cost (NB M T β c₂ ε) L ≤ c₄B M T α β c₁ c₂ c₃ * ε ^ (-2 : ℝ) := by
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) < M := by linarith
  have hMpos : (0 : ℝ) < M := by linarith
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = (β - 1) / 2 := ⟨_, rfl⟩
  have hγpos : 0 < γ := by rw [hγ]; linarith
  have e1 : (β - 1) / 2 = γ := hγ.symm
  have e2 : -(β - 1) / 2 = -γ := by rw [hγ]; ring
  have e3 : (β + 1) / 2 = γ + 1 := by rw [hγ]; ring
  have e5 : β - 1 = γ + γ := by rw [hγ]; ring
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (M : ℝ) ^ (-γ) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact Real.rpow_pos_of_pos hMpos _
  have hr1 : r < 1 := by rw [hr]; exact Real.rpow_lt_one_of_one_lt_of_neg hM1 (by linarith)
  have hκ : 0 < 1 - r := by linarith
  have hh : ∀ l, 0 < h M T l := by intro l; unfold h; positivity
  have hR : 0 < ε ^ (-2 : ℝ) := Real.rpow_pos_of_pos hε _
  have hTγ : 0 < T ^ γ := Real.rpow_pos_of_pos hT _
  have h7 := gmc_eq7 M hM T hT α c₁ ε hα hc₁ hε hε1 L hL
  set R : ℝ := ε ^ (-2 : ℝ) with hRdef
  set B : ℝ := (Real.sqrt 2 * c₁) ^ (1 / α) with hB
  set K : ℝ := 2 * R * c₂ * T ^ γ * (1 - r)⁻¹ with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  set a : ℕ → ℝ := fun l => K * h M T l ^ (γ + 1) with ha
  have hapos : ∀ l, 0 < a l := by
    intro l
    have := Real.rpow_pos_of_pos (hh l) (γ + 1)
    rw [ha]; simp only; positivity
  have hNB : ∀ l, NB M T β c₂ ε l = ⌈a l⌉₊ := by
    intro l
    simp only [NB, ha, hK]
    rw [e1, e2, e3, ← hr]
  have hN1 : ∀ l, 1 ≤ NB M T β c₂ ε l := fun l => by
    rw [hNB]; exact Nat.one_le_ceil_iff.mpr (hapos l)
  have hNle : ∀ l, (NB M T β c₂ ε l : ℝ) ≤ a l + 1 := fun l => by
    rw [hNB]; exact (Nat.ceil_lt_add_one (hapos l).le).le
  have hhγ : ∀ l, h M T l ^ γ = T ^ γ * r ^ l := by
    intro l
    have hml : (0 : ℝ) < (M : ℝ) ^ l := by positivity
    have e : r ^ l = (((M : ℝ) ^ l) ^ γ)⁻¹ := by
      rw [hr, ← Real.rpow_natCast ((M : ℝ) ^ (-γ)) l, ← Real.rpow_mul hMpos.le,
        ← Real.rpow_natCast (M : ℝ) l, ← Real.rpow_mul hMpos.le]
      rw [show -γ * (l : ℝ) = -((l : ℝ) * γ) by ring, Real.rpow_neg hMpos.le]
    rw [e]
    unfold h
    rw [Real.div_rpow hT.le hml.le, div_eq_mul_inv]
  have hterm : ∀ l, cost l (NB M T β c₂ ε l) ≤ c₃ * (K * (T ^ γ * r ^ l)) + c₃ * (h M T l)⁻¹ := by
    intro l
    have hhl := hh l
    refine (h_iv l _ (hN1 l)).trans ?_
    calc c₃ * ((NB M T β c₂ ε l : ℕ) : ℝ) * (h M T l)⁻¹
        ≤ c₃ * (a l + 1) * (h M T l)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hhl.le)
          exact mul_le_mul_of_nonneg_left (hNle l) hc₃.le
      _ = c₃ * (K * h M T l ^ γ) + c₃ * (h M T l)⁻¹ := by
          have : h M T l ^ (γ + 1) = h M T l ^ γ * h M T l := by
            rw [Real.rpow_add hhl, Real.rpow_one]
          have hak : a l = K * h M T l ^ (γ + 1) := rfl
          rw [hak, this]
          field_simp
      _ = _ := by rw [hhγ l]
  have hgeom : ∑ l ∈ Finset.range (L + 1), r ^ l ≤ (1 - r)⁻¹ := by
    have := geom_sum_mul_neg r (L + 1)
    have h2 : (∑ l ∈ Finset.range (L + 1), r ^ l) * (1 - r) ≤ 1 := by
      rw [this]; have : 0 < r ^ (L + 1) := pow_pos hr0 _; linarith
    rw [← one_div]
    exact (le_div_iff₀ hκ).mpr h2
  have hTT : T ^ (β - 1) = T ^ γ * T ^ γ := by rw [e5, Real.rpow_add hT]
  unfold c₄B
  rw [e2, ← hr, hTT]
  calc totalCost cost (NB M T β c₂ ε) L
      ≤ ∑ l ∈ Finset.range (L + 1), (c₃ * (K * (T ^ γ * r ^ l)) + c₃ * (h M T l)⁻¹) :=
        Finset.sum_le_sum (fun l _ => hterm l)
    _ = c₃ * (K * T ^ γ) * ∑ l ∈ Finset.range (L + 1), r ^ l
          + c₃ * ∑ l ∈ Finset.range (L + 1), (h M T l)⁻¹ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
          Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl; intro l _; ring
    _ ≤ c₃ * (K * T ^ γ) * (1 - r)⁻¹
          + c₃ * ((M : ℝ) ^ 2 / ((M : ℝ) - 1) * B * R) := by
        have h1 : 0 ≤ c₃ * (K * T ^ γ) := by positivity
        have h2 := mul_le_mul_of_nonneg_left hgeom h1
        have h4 := mul_le_mul_of_nonneg_left h7.le hc₃.le
        linarith
    _ = _ := by
        rw [hK, ← hB]
        field_simp
