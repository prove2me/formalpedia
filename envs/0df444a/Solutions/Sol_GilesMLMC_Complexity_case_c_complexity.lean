-- Prove2me | solution 1 for GilesMLMC.Complexity.case_c_complexity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:56:19.536305+00:00
-- url     : https://prove2.me/submissions/71ecc39f-effd-4c7f-8160-022b7f4d9424

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

lemma gmc_hLinv
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (α c₁ ε : ℝ) (hα : 1 / 2 ≤ α) (hc₁ : 0 < c₁) (hε : 0 < ε)
    (L : ℕ) (hL : (L : ℤ) = Lchoice M T α c₁ ε) :
    (h M T L)⁻¹ < (M : ℝ) * (Real.sqrt 2 * c₁) ^ (1 / α) * (ε ^ (1 / α))⁻¹ := by
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) < M := by linarith
  have hMpos : (0 : ℝ) < M := by linarith
  have hαpos : 0 < α := by linarith
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos hM1
  set B : ℝ := (Real.sqrt 2 * c₁) ^ (1 / α) with hB
  set A : ℝ := Real.sqrt 2 * c₁ * T ^ α * ε⁻¹ with hA
  have hApos : 0 < A := by
    rw [hA]
    have := Real.rpow_pos_of_pos hT α
    have : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  set x : ℝ := Real.log A / (α * Real.log (M : ℝ)) with hx
  have hLx : (L : ℝ) < x + 1 := by
    have h1 : ((L : ℤ) : ℝ) = (Lchoice M T α c₁ ε : ℝ) := by rw [hL]
    have h2 : (Lchoice M T α c₁ ε : ℝ) < x + 1 := by
      have := Int.ceil_lt_add_one x
      simpa [Lchoice, hx, hA] using this
    simpa using h1.trans_lt h2
  have hMx : (M : ℝ) ^ x = A ^ (1 / α) := by
    rw [Real.rpow_def_of_pos hMpos, Real.rpow_def_of_pos hApos]
    congr 1
    rw [hx]
    field_simp
  have hAexp : A ^ (1 / α) = B * T * (ε ^ (1 / α))⁻¹ := by
    rw [hA, hB]
    rw [Real.mul_rpow (by
        have := Real.rpow_pos_of_pos hT α
        have : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
        positivity) (inv_nonneg.mpr hε.le),
      Real.mul_rpow (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hc₁).le
        (Real.rpow_nonneg hT.le _),
      ← Real.rpow_mul hT.le, Real.inv_rpow hε.le]
    rw [mul_one_div_cancel hαpos.ne', Real.rpow_one]
  have h1 : (M : ℝ) ^ ((L : ℝ)) < (M : ℝ) ^ (x + 1) :=
    Real.rpow_lt_rpow_of_exponent_lt hM1 hLx
  have h2 : (M : ℝ) ^ ((L : ℝ)) = (M : ℝ) ^ L := Real.rpow_natCast _ _
  have h3 : (M : ℝ) ^ (x + 1) = (M : ℝ) ^ x * M := by
    rw [Real.rpow_add hMpos, Real.rpow_one]
  rw [h2, h3, hMx, hAexp] at h1
  have hinv : (h M T L)⁻¹ = (M : ℝ) ^ L / T := by
    simp [h, inv_div]
  rw [hinv, div_lt_iff₀ hT]
  calc (M : ℝ) ^ L < B * T * (ε ^ (1 / α))⁻¹ * M := h1
    _ = _ := by ring

theorem solution
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (α β c₁ c₂ c₃ : ℝ) (hα : 1 / 2 ≤ α) (hβ : 0 < β) (hβ1 : β < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (cost : ℕ → ℕ → ℝ) (h_iv : ∀ l N, 1 ≤ N → cost l N ≤ c₃ * N * (h M T l)⁻¹)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < Real.exp (-1))
    (L : ℕ) (hL : (L : ℤ) = Lchoice M T α c₁ ε) :
    totalCost cost (NC M T β c₂ ε L) L ≤ c₄C M α β c₁ c₂ c₃ * ε ^ (-2 - (1 - β) / α) := by
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) < M := by linarith
  have hMpos : (0 : ℝ) < M := by linarith
  have hαpos : 0 < α := by linarith
  have hε1' : ε < 1 := by
    have : Real.exp (-1) < Real.exp 0 := Real.exp_lt_exp.mpr (by norm_num)
    rw [Real.exp_zero] at this
    linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (1 - β) / 2 := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have e2 : -(1 - β) / 2 = -δ := by rw [hδ]; ring
  have e3 : (β + 1) / 2 = 1 - δ := by rw [hδ]; ring
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (M : ℝ) ^ (-δ) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact Real.rpow_pos_of_pos hMpos _
  have hr1 : r < 1 := by rw [hr]; exact Real.rpow_lt_one_of_one_lt_of_neg hM1 (by linarith)
  have hκ : 0 < 1 - r := by linarith
  have hh : ∀ l, 0 < h M T l := by intro l; unfold h; positivity
  have hR : 0 < ε ^ (-2 : ℝ) := Real.rpow_pos_of_pos hε _
  have hTδ : 0 < T ^ (-δ) := Real.rpow_pos_of_pos hT _
  have h7 := gmc_eq7 M hM T hT α c₁ ε hα hc₁ hε hε1 L hL
  have hLi := gmc_hLinv M hM T hT α c₁ ε hα hc₁ hε L hL
  set R : ℝ := ε ^ (-2 : ℝ) with hRdef
  set B : ℝ := (Real.sqrt 2 * c₁) ^ (1 / α) with hB
  have hBpos : 0 < B := by
    rw [hB]
    apply Real.rpow_pos_of_pos
    exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) hc₁
  have hhδ : ∀ l, h M T l ^ (-δ) = T ^ (-δ) / r ^ l := by
    intro l
    have hml : (0 : ℝ) < (M : ℝ) ^ l := by positivity
    have e : r ^ l = ((M : ℝ) ^ l) ^ (-δ) := by
      rw [hr, ← Real.rpow_natCast ((M : ℝ) ^ (-δ)) l, ← Real.rpow_mul hMpos.le,
        ← Real.rpow_natCast (M : ℝ) l, ← Real.rpow_mul hMpos.le]
      congr 1; ring
    rw [e]
    unfold h
    rw [Real.div_rpow hT.le hml.le]
  have hLl : ∀ l, l ≤ L → h M T l ^ (-δ) = h M T L ^ (-δ) * r ^ (L - l) := by
    intro l hl
    rw [hhδ l, hhδ L, pow_sub₀ r hr0.ne' hl]
    have : 0 < r ^ l := pow_pos hr0 _
    have : 0 < r ^ L := pow_pos hr0 _
    field_simp
  have hHL : 0 < h M T L ^ (-δ) := Real.rpow_pos_of_pos (hh L) _
  set J : ℝ := 2 * R * c₂ * h M T L ^ (-δ) * (1 - r)⁻¹ with hJ
  have hJpos : 0 < J := by rw [hJ]; positivity
  set a : ℕ → ℝ := fun l => J * h M T l ^ (1 - δ) with ha
  have hapos : ∀ l, 0 < a l := by
    intro l
    have := Real.rpow_pos_of_pos (hh l) (1 - δ)
    rw [ha]; simp only; positivity
  have hNC : ∀ l, NC M T β c₂ ε L l = ⌈a l⌉₊ := by
    intro l
    simp only [NC, ha, hJ]
    rw [e2, e3, ← hr]
  have hN1 : ∀ l, 1 ≤ NC M T β c₂ ε L l := fun l => by
    rw [hNC]; exact Nat.one_le_ceil_iff.mpr (hapos l)
  have hNle : ∀ l, (NC M T β c₂ ε L l : ℝ) ≤ a l + 1 := fun l => by
    rw [hNC]; exact (Nat.ceil_lt_add_one (hapos l).le).le
  have hterm : ∀ l, l ≤ L → cost l (NC M T β c₂ ε L l) ≤
      c₃ * (J * h M T L ^ (-δ) * r ^ (L - l)) + c₃ * (h M T l)⁻¹ := by
    intro l hl
    have hhl := hh l
    refine (h_iv l _ (hN1 l)).trans ?_
    calc c₃ * ((NC M T β c₂ ε L l : ℕ) : ℝ) * (h M T l)⁻¹
        ≤ c₃ * (a l + 1) * (h M T l)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hhl.le)
          exact mul_le_mul_of_nonneg_left (hNle l) hc₃.le
      _ = c₃ * (J * h M T l ^ (-δ)) + c₃ * (h M T l)⁻¹ := by
          have : h M T l ^ (1 - δ) = h M T l ^ (-δ) * h M T l := by
            rw [show 1 - δ = -δ + 1 by ring, Real.rpow_add hhl, Real.rpow_one]
          have hak : a l = J * h M T l ^ (1 - δ) := rfl
          rw [hak, this]
          field_simp
      _ = _ := by rw [hLl l hl]; ring
  have hgeom : ∑ l ∈ Finset.range (L + 1), r ^ (L - l) ≤ (1 - r)⁻¹ := by
    have hrefl : ∑ l ∈ Finset.range (L + 1), r ^ (L - l) = ∑ l ∈ Finset.range (L + 1), r ^ l := by
      have := Finset.sum_range_reflect (fun j => r ^ j) (L + 1)
      simpa using this
    rw [hrefl]
    have := geom_sum_mul_neg r (L + 1)
    have h2 : (∑ l ∈ Finset.range (L + 1), r ^ l) * (1 - r) ≤ 1 := by
      rw [this]; have : 0 < r ^ (L + 1) := pow_pos hr0 _; linarith
    rw [← one_div]
    exact (le_div_iff₀ hκ).mpr h2
  -- the bound on h_L^{-(1-β)}
  set E : ℝ := ε ^ (-((1 - β) / α)) with hE
  have hE1 : 1 ≤ E :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1'.le (by
      have : 0 ≤ (1 - β) / α := div_nonneg (by linarith) hαpos.le
      linarith)
  have hRE : ε ^ (-2 - (1 - β) / α) = R * E := by
    rw [hRdef, hE, ← Real.rpow_add hε]; congr 1
  have hQ : (h M T L ^ (-δ)) ^ 2 ≤
      (M : ℝ) ^ (1 - β) * (Real.sqrt 2 * c₁) ^ ((1 - β) / α) * E := by
    have h1 : (h M T L ^ (-δ)) ^ 2 = ((h M T L)⁻¹) ^ (1 - β) := by
      rw [sq, ← Real.rpow_add (hh L), show -δ + -δ = -(1 - β) by rw [hδ]; ring,
        Real.rpow_neg (hh L).le, Real.inv_rpow (hh L).le]
    rw [h1]
    have hsq : 0 < Real.sqrt 2 * c₁ := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hc₁
    have hεp : 0 < (ε ^ (1 / α))⁻¹ := inv_pos.mpr (Real.rpow_pos_of_pos hε _)
    have h2 : ((h M T L)⁻¹) ^ (1 - β) ≤
        ((M : ℝ) * B * (ε ^ (1 / α))⁻¹) ^ (1 - β) :=
      Real.rpow_le_rpow (inv_nonneg.mpr (hh L).le) hLi.le (by linarith)
    refine h2.trans (le_of_eq ?_)
    rw [Real.mul_rpow (by positivity) hεp.le, Real.mul_rpow hMpos.le hBpos.le, hB,
      ← Real.rpow_mul hsq.le, Real.inv_rpow (Real.rpow_pos_of_pos hε _).le,
      ← Real.rpow_mul hε.le, hE, Real.rpow_neg hε.le,
      show 1 / α * (1 - β) = (1 - β) / α by ring]
  unfold c₄C
  rw [hRE, e2, ← hr]
  have hX : 0 ≤ (M : ℝ) ^ 2 / ((M : ℝ) - 1) * B * R := by positivity
  calc totalCost cost (NC M T β c₂ ε L) L
      ≤ ∑ l ∈ Finset.range (L + 1),
          (c₃ * (J * h M T L ^ (-δ) * r ^ (L - l)) + c₃ * (h M T l)⁻¹) := by
        apply Finset.sum_le_sum
        intro l hl
        exact hterm l (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl))
    _ = c₃ * (J * h M T L ^ (-δ)) * ∑ l ∈ Finset.range (L + 1), r ^ (L - l)
          + c₃ * ∑ l ∈ Finset.range (L + 1), (h M T l)⁻¹ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl; intro l _; ring
    _ ≤ c₃ * (J * h M T L ^ (-δ)) * (1 - r)⁻¹
          + c₃ * ((M : ℝ) ^ 2 / ((M : ℝ) - 1) * B * R) := by
        have h1 : 0 ≤ c₃ * (J * h M T L ^ (-δ)) := by positivity
        have h2 := mul_le_mul_of_nonneg_left hgeom h1
        have h4 := mul_le_mul_of_nonneg_left h7.le hc₃.le
        linarith
    _ = 2 * c₃ * c₂ * R * (h M T L ^ (-δ)) ^ 2 * ((1 - r)⁻¹) ^ 2
          + c₃ * ((M : ℝ) ^ 2 / ((M : ℝ) - 1) * B * R) := by
        rw [hJ]; ring
    _ ≤ 2 * c₃ * c₂ * R * ((M : ℝ) ^ (1 - β) * (Real.sqrt 2 * c₁) ^ ((1 - β) / α) * E)
            * ((1 - r)⁻¹) ^ 2
          + c₃ * ((M : ℝ) ^ 2 / ((M : ℝ) - 1) * B * R) := by
        have h0 : 0 ≤ 2 * c₃ * c₂ * R * ((1 - r)⁻¹) ^ 2 := by positivity
        have := mul_le_mul_of_nonneg_left hQ h0
        linarith
    _ ≤ _ := by
        have h5 : c₃ * ((M : ℝ) ^ 2 / ((M : ℝ) - 1) * B * R) ≤
            c₃ * ((M : ℝ) ^ 2 / ((M : ℝ) - 1) * B * R) * E := by
          have := mul_nonneg hc₃.le hX
          nlinarith
        have h6 : 2 * c₃ * c₂ * R * ((M : ℝ) ^ (1 - β) * (Real.sqrt 2 * c₁) ^ ((1 - β) / α) * E)
            * ((1 - r)⁻¹) ^ 2 =
            2 * c₃ * c₂ * (Real.sqrt 2 * c₁) ^ ((1 - β) / α) * (M : ℝ) ^ (1 - β)
              * ((1 - r)⁻¹) ^ 2 * (R * E) := by ring
        have h8 : c₃ * ((M : ℝ) ^ 2 / ((M : ℝ) - 1)) * B * (R * E) =
            c₃ * ((M : ℝ) ^ 2 / ((M : ℝ) - 1) * B * R) * E := by ring
        linarith [h5, h6, h8]
