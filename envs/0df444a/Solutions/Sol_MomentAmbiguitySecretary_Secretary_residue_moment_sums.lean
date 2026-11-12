-- Prove2me | solution 1 for MomentAmbiguitySecretary.Secretary.residue_moment_sums
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:17:58.173197+00:00
-- url     : https://prove2.me/submissions/69fe1a09-f6a5-4b16-83c8-0ad628d5bb62

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Separator
import Theorems.Thm_MomentAmbiguitySecretary_Secretary_entire_product_coefficients

section
open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal

namespace MomentAmbiguitySecretary.Secretary.Dev.ResidueSums

open MomentAmbiguitySecretary.Secretary

lemma geom_unit (N : ℕ) (x : ℂ) (hx : x ^ N = 1) :
    ∑ l ∈ Finset.range N, x ^ l = if x = 1 then (N : ℂ) else 0 := by
  split_ifs with h
  · subst h; simp
  · rw [geom_sum_eq h, hx]; simp

lemma factor_zero (B N : ℕ) (hB : 2 ≤ B) (t l : ℕ) (hl0 : l ≠ 0) (hl : l < N) :
    factor B N t (Complex.exp (2 * Real.pi * Complex.I / N) ^ l * (B : ℂ) ^ t) = 0 := by
  have hN : N ≠ 0 := by omega
  have hω := Complex.isPrimitiveRoot_exp N hN
  have hB0 : (B : ℂ) ≠ 0 := by exact_mod_cast (by omega : B ≠ 0)
  have h1 : Complex.exp (2 * Real.pi * Complex.I / N) ^ l ≠ 1 := by
    intro h
    rw [hω.pow_eq_one_iff_dvd] at h
    exact hl0 (Nat.eq_zero_of_dvd_of_lt h hl)
  unfold factor
  rw [Fin.sum_univ_eq_sum_range (fun u => (Complex.exp (2 * Real.pi * Complex.I / N) ^ l *
    (B : ℂ) ^ t * (B : ℂ)⁻¹ ^ t) ^ u) N]
  have : Complex.exp (2 * Real.pi * Complex.I / N) ^ l * (B : ℂ) ^ t * (B : ℂ)⁻¹ ^ t =
      Complex.exp (2 * Real.pi * Complex.I / N) ^ l := by
    rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hB0, one_pow, mul_one]
  have hx : (Complex.exp (2 * Real.pi * Complex.I / N) ^ l) ^ N = 1 := by
    rw [pow_right_comm, hω.pow_eq_one, one_pow]
  rw [this, geom_unit N _ hx]
  simp [h1]

lemma G_zero (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) (t l : ℕ) (hl0 : l ≠ 0) (hl : l < N) :
    entireProduct B N (Complex.exp (2 * Real.pi * Complex.I / N) ^ l * (B : ℂ) ^ t) = 0 := by
  have h1 := (entire_product_coefficients B N hB hN).1.tendsto_at (mem_univ
    (Complex.exp (2 * Real.pi * Complex.I / N) ^ l * (B : ℂ) ^ t))
  have h2 : ∀ᶠ M : ℕ in atTop, finiteProduct B N M
      (Complex.exp (2 * Real.pi * Complex.I / N) ^ l * (B : ℂ) ^ t) = 0 := by
    filter_upwards [eventually_ge_atTop t] with M hM
    unfold finiteProduct
    exact Finset.prod_eq_zero (i := ⟨t, by omega⟩) (Finset.mem_univ _)
      (factor_zero B N hB t l hl0 hl)
  exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr' (h2.mono fun M h => h.symm))

lemma finiteOccupancySum_nonneg (B N M j : ℕ) : 0 ≤ finiteOccupancySum B N M j := by
  unfold finiteOccupancySum
  refine Finset.sum_nonneg fun c _ => ?_
  split_ifs
  · positivity
  · exact le_rfl

lemma coef_nonneg (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) (j : ℕ) : 0 ≤ coefficient B N j :=
  ge_of_tendsto' ((entire_product_coefficients B N hB hN).2.2.2.2.2 j).2.1
    fun M => finiteOccupancySum_nonneg B N M j

lemma G_zero_pt (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) : entireProduct B N 0 = 1 := by
  have h1 := (entire_product_coefficients B N hB hN).1.tendsto_at (mem_univ (0 : ℂ))
  have h2 : ∀ M, finiteProduct B N M 0 = 1 := by
    intro M
    unfold finiteProduct factor
    refine Finset.prod_eq_one fun m _ => ?_
    rw [Fin.sum_univ_eq_sum_range (fun u => ((0 : ℂ) * (B : ℂ)⁻¹ ^ (m : ℕ)) ^ u) N]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; simp at h; omega
  simp_rw [h2] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

lemma coef_zero (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) : coefficient B N 0 = 1 := by
  have h := (entire_product_coefficients B N hB hN).2.2.2.2.1 0
  have h' : HasSum (fun j => (coefficient B N j : ℂ) * (0 : ℂ) ^ j) (coefficient B N 0 : ℂ) := by
    have := hasSum_single (f := fun j => (coefficient B N j : ℂ) * (0 : ℂ) ^ j) 0
      (by intro j hj; simp [hj])
    simpa using this
  have := h.unique h'
  rw [G_zero_pt B N hB hN] at this
  exact_mod_cast this.symm

lemma summable_a (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) (t : ℕ) :
    Summable (fun j => coefficient B N j * (B : ℝ) ^ (t * j)) := by
  have := ((entire_product_coefficients B N hB hN).2.2.2.2.1 ((B : ℂ) ^ t)).summable
  refine (Complex.summable_ofReal (f := fun j => coefficient B N j * (B : ℝ) ^ (t * j))).mp ?_
  convert this using 2 with j
  push_cast
  rw [pow_mul]

lemma residueTerm_nonneg (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) (h t j : ℕ) :
    0 ≤ residueTerm B N h t j := by
  unfold residueTerm
  split_ifs
  · have := coef_nonneg B N hB hN j
    positivity
  · exact le_rfl

lemma summable_residueTerm (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) (h t : ℕ) :
    Summable (residueTerm B N h t) := by
  refine Summable.of_nonneg_of_le (residueTerm_nonneg B N hB hN h t) (fun j => ?_)
    (summable_a B N hB hN t)
  unfold residueTerm
  split_ifs
  · exact le_rfl
  · have := coef_nonneg B N hB hN j
    positivity

lemma fourier (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) (t h : ℕ) (hh : h < N) :
    (N : ℂ) * (residueSum B N h t : ℂ) = entireProduct B N ((B : ℂ) ^ t) := by
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / N) with hωdef
  have hN0 : N ≠ 0 := by omega
  have hω : IsPrimitiveRoot ω N := Complex.isPrimitiveRoot_exp N hN0
  have hl : ∀ l ∈ Finset.range N, HasSum (fun j : ℕ => ((ω ^ h)⁻¹) ^ l *
      ((coefficient B N j : ℂ) * (ω ^ l * (B : ℂ) ^ t) ^ j))
      (((ω ^ h)⁻¹) ^ l * entireProduct B N (ω ^ l * (B : ℂ) ^ t)) := fun l _ =>
    ((entire_product_coefficients B N hB hN).2.2.2.2.1 _).mul_left _
  have hs := hasSum_sum hl
  rw [Finset.sum_eq_single 0 (fun l hl hl0 => by
      rw [G_zero B N hB hN t l hl0 (Finset.mem_range.mp hl), mul_zero]) (by simp; omega)] at hs
  simp only [pow_zero, one_mul, one_mul] at hs
  have hs2 : HasSum (fun j : ℕ => (N : ℂ) * (residueTerm B N h t j : ℂ))
      (entireProduct B N ((B : ℂ) ^ t)) := by
    convert hs using 1
    funext j
    have e : ∀ l : ℕ, ((ω ^ h)⁻¹) ^ l * ((coefficient B N j : ℂ) * (ω ^ l * (B : ℂ) ^ t) ^ j) =
        (coefficient B N j : ℂ) * (B : ℂ) ^ (t * j) * (ω ^ j * (ω ^ h)⁻¹) ^ l := by
      intro l
      rw [pow_mul (B : ℂ) t j, mul_pow, pow_right_comm ω l j, mul_pow]
      ring
    simp_rw [e]
    rw [← Finset.mul_sum, geom_unit N _ (by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm j N, mul_comm h N, pow_mul, pow_mul,
        hω.pow_eq_one, one_pow, one_pow]; simp)]
    unfold residueTerm
    have key : (ω ^ j * (ω ^ h)⁻¹ = 1) ↔ j % N = h := by
      rw [mul_inv_eq_one₀ (pow_ne_zero _ (hω.ne_zero hN0)), (isOfFinOrder_iff_pow_eq_one.mpr ⟨N, by omega, hω.pow_eq_one⟩).pow_eq_pow_iff_modEq,
        ← hω.eq_orderOf]
      unfold Nat.ModEq
      rw [Nat.mod_eq_of_lt hh]
    by_cases hj : j % N = h
    · simp [hj, key.mpr hj]; rw [pow_mul]; ring
    · simp [hj, mt key.mp hj]
  have hr := ((summable_residueTerm B N hB hN h t).hasSum)
  have hr2 : HasSum (fun j : ℕ => (N : ℂ) * (residueTerm B N h t j : ℂ))
      ((N : ℂ) * (residueSum B N h t : ℂ)) :=
    (Complex.hasSum_ofReal.mpr hr).mul_left _
  exact hr2.unique hs2

lemma P_bound (M : ℕ) : (9 : ℝ) / 32 ≤ ∏ m ∈ Finset.range M, (1 - (1 / 2 : ℝ) ^ (m + 1)) := by
  have key : ∀ M, 2 ≤ M → (3 : ℝ) / 8 * (3 / 4 + (1 / 2) ^ M) ≤
      ∏ m ∈ Finset.range M, (1 - (1 / 2 : ℝ) ^ (m + 1)) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => norm_num [Finset.prod_range_succ]
    | succ n hn ih =>
      rw [Finset.prod_range_succ]
      have hp : (0 : ℝ) < (1 / 2) ^ n := by positivity
      have hp1 : (1 / 2 : ℝ) ^ n ≤ 1 / 4 := by
        calc (1 / 2 : ℝ) ^ n ≤ (1 / 2) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
          _ = 1 / 4 := by norm_num
      have hq : (1 - (1 / 2 : ℝ) ^ (n + 1)) ≥ 0 := by
        have : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 / 4 * (1 / 2) := by
          rw [pow_succ]; nlinarith
        linarith
      calc (3 : ℝ) / 8 * (3 / 4 + (1 / 2) ^ (n + 1))
          ≤ (3 / 8 * (3 / 4 + (1 / 2) ^ n)) * (1 - (1 / 2) ^ (n + 1)) := by
            rw [pow_succ]; nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_right ih hq
  rcases Nat.lt_or_ge M 2 with h | h
  · interval_cases M <;> norm_num [Finset.prod_range_succ]
  · refine le_trans ?_ (key M h)
    have : (0 : ℝ) < (1 / 2) ^ M := by positivity
    have h1 : (1 / 2 : ℝ) ^ M ≤ 1 / 4 := by
      calc (1 / 2 : ℝ) ^ M ≤ (1 / 2) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) h
        _ = 1 / 4 := by norm_num
    nlinarith

lemma finiteProduct_one_real (B N M : ℕ) :
    finiteProduct B N M 1 = (((∏ m ∈ Finset.range (M + 1),
      ∑ u ∈ Finset.range N, ((B : ℝ)⁻¹ ^ m) ^ u : ℝ)) : ℂ) := by
  unfold finiteProduct factor
  rw [Fin.prod_univ_eq_prod_range (fun m => ∑ u : Fin N, (1 * (B : ℂ)⁻¹ ^ m) ^ (u : ℕ)) (M + 1)]
  push_cast
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [Fin.sum_univ_eq_sum_range (fun u => (1 * (B : ℂ)⁻¹ ^ m) ^ u) N]
  simp

lemma R_le (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) (M : ℕ) :
    (∏ m ∈ Finset.range (M + 1), ∑ u ∈ Finset.range N, ((B : ℝ)⁻¹ ^ m) ^ u) ≤ N * (32 / 9) := by
  rw [Finset.prod_range_succ']
  suffices hP : ∏ m ∈ Finset.range M, ∑ u ∈ Finset.range N, ((B : ℝ)⁻¹ ^ (m + 1)) ^ u ≤ 32 / 9 by
    simp only [pow_zero, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have : (0 : ℝ) ≤ N := by positivity
    nlinarith
  have hB2 : (B : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast hB)
  have hb0 : (0 : ℝ) ≤ (B : ℝ)⁻¹ := by positivity
  have hx : ∀ m : ℕ, ((B : ℝ)⁻¹ ^ (m + 1)) ≤ (1 / 2) ^ (m + 1) :=
    fun m => pow_le_pow_left₀ hb0 hB2 _
  have hx1 : ∀ m : ℕ, (1 / 2 : ℝ) ^ (m + 1) ≤ 1 / 2 := fun m =>
    pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  have step : ∀ m ∈ Finset.range M,
      ∑ u ∈ Finset.range N, ((B : ℝ)⁻¹ ^ (m + 1)) ^ u ≤ (1 - (1 / 2 : ℝ) ^ (m + 1))⁻¹ := by
    intro m _
    have h1 := hx m
    have h2 := hx1 m
    have h0 : (0 : ℝ) < 1 - (B : ℝ)⁻¹ ^ (m + 1) := by linarith
    have h3 : (0 : ℝ) < 1 - (1 / 2 : ℝ) ^ (m + 1) := by linarith
    have hpow : 0 ≤ ((B : ℝ)⁻¹ ^ (m + 1)) ^ N := by positivity
    have hs := geom_sum_mul_neg ((B : ℝ)⁻¹ ^ (m + 1)) N
    have hle : (∑ u ∈ Finset.range N, ((B : ℝ)⁻¹ ^ (m + 1)) ^ u) ≤ (1 - (B : ℝ)⁻¹ ^ (m + 1))⁻¹ := by
      refine le_of_mul_le_mul_right ?_ h0
      rw [hs, inv_mul_cancel₀ h0.ne']
      linarith
    exact hle.trans (inv_anti₀ h3 (by linarith))
  calc ∏ m ∈ Finset.range M, ∑ u ∈ Finset.range N, ((B : ℝ)⁻¹ ^ (m + 1)) ^ u
      ≤ ∏ m ∈ Finset.range M, (1 - (1 / 2 : ℝ) ^ (m + 1))⁻¹ :=
        Finset.prod_le_prod (fun m _ => Finset.sum_nonneg fun u _ => by positivity) step
    _ = (∏ m ∈ Finset.range M, (1 - (1 / 2 : ℝ) ^ (m + 1)))⁻¹ := by rw [Finset.prod_inv_distrib]
    _ ≤ ((9 : ℝ) / 32)⁻¹ := inv_anti₀ (by norm_num) (P_bound M)
    _ = 32 / 9 := by norm_num

lemma normalizer_cast (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    (N : ℂ) * (normalizer B N : ℂ) = entireProduct B N 1 := by
  have := fourier B N hB hN 0 0 (by omega)
  simpa [normalizer] using this

lemma normalizer_ge (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) : 1 ≤ normalizer B N := by
  have := (summable_residueTerm B N hB hN 0 0).le_tsum 0
    (fun j _ => residueTerm_nonneg B N hB hN 0 0 j)
  have h0 : residueTerm B N 0 0 0 = 1 := by simp [residueTerm, coef_zero B N hB hN]
  rw [h0] at this
  exact this

lemma normalizer_lt (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) : normalizer B N < 4 := by
  have hT : Tendsto (fun M : ℕ => (finiteProduct B N M 1).re) atTop
      (𝓝 (entireProduct B N 1).re) :=
    (Complex.continuous_re.tendsto _).comp
      ((entire_product_coefficients B N hB hN).1.tendsto_at (mem_univ (1 : ℂ)))
  have hre : (entireProduct B N 1).re = N * normalizer B N := by
    rw [← normalizer_cast B N hB hN]; simp
  rw [hre] at hT
  have hle : (N : ℝ) * normalizer B N ≤ N * (32 / 9) := by
    refine le_of_tendsto' hT fun M => ?_
    rw [finiteProduct_one_real, Complex.ofReal_re]
    exact R_le B N hB hN M
  have hNp : (0 : ℝ) < N := by positivity
  have := le_of_mul_le_mul_left hle hNp
  linarith

end MomentAmbiguitySecretary.Secretary.Dev.ResidueSums

namespace MomentAmbiguitySecretary.Secretary

open MomentAmbiguitySecretary.Secretary.Dev.ResidueSums

theorem chk_residue_moment_sums (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    (∀ (t : ℕ) (h : Fin N),
      HasSum (residueTerm B N h.val t) (residueSum B N h.val t) ∧
      (residueSum B N h.val t : ℂ) = entireProduct B N ((B : ℂ) ^ t) / (N : ℂ)) ∧
    (∀ h : Fin N, residueSum B N h.val 0 = normalizer B N) ∧
    1 ≤ normalizer B N ∧ normalizer B N < 4 := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  refine ⟨fun t h => ⟨(summable_residueTerm B N hB hN h.val t).hasSum, ?_⟩, fun h => ?_,
    normalizer_ge B N hB hN, normalizer_lt B N hB hN⟩
  · rw [eq_div_iff hN0, mul_comm]; exact fourier B N hB hN t h.val h.isLt
  · have h1 := fourier B N hB hN 0 h.val h.isLt
    have h2 := normalizer_cast B N hB hN
    rw [pow_zero] at h1
    have : (N : ℂ) * (residueSum B N h.val 0 : ℂ) = (N : ℂ) * (normalizer B N : ℂ) := by
      rw [h1, h2]
    exact_mod_cast mul_left_cancel₀ hN0 this

end MomentAmbiguitySecretary.Secretary

end

theorem solution : type_of% @MomentAmbiguitySecretary.Secretary.chk_residue_moment_sums := @MomentAmbiguitySecretary.Secretary.chk_residue_moment_sums
