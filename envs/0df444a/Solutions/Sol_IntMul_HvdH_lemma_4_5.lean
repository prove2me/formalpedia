-- Prove2me | solution 1 for IntMul.HvdH.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @avi
-- created : 2026-10-08T23:16:23.502151+00:00
-- url     : https://prove2.me/submissions/b7bc5cea-f9f6-4417-b76b-0f6b84f6f237

import Mathlib
import Definitions.Def_IntMul_HvdH_Resampling

open Complex Real MeasureTheory Set IntMul.HvdH

namespace IntMulLemma45

/-- Poisson summation for a shifted Gaussian:
`∑ⱼ exp(-π (j - x)² / α²) = α · θ₂(-x, iα²)`. -/
lemma gauss_shift_eq (α : ℝ) (hα : 0 < α) (x : ℝ) :
    ((∑' j : ℤ, rexp (-π * ((j : ℝ) - x) ^ 2 / α ^ 2) : ℝ) : ℂ) =
      (α : ℂ) * ∑' n : ℤ, jacobiTheta₂_term n (-x) (I * (α : ℂ) ^ 2) := by
  have hα2 : (0 : ℝ) < α ^ 2 := by positivity
  have ha : 0 < ((1 / α ^ 2 : ℝ) : ℂ).re := by simp only [ofReal_re]; positivity
  have h := Complex.tsum_exp_neg_quadratic ha ((x / α ^ 2 : ℝ) : ℂ)
  -- left side: pull out the constant factor exp(-π x²/α²)
  have hL : ((∑' j : ℤ, rexp (-π * ((j : ℝ) - x) ^ 2 / α ^ 2) : ℝ) : ℂ) =
      cexp (-π * x ^ 2 / α ^ 2) *
        ∑' n : ℤ, cexp (-π * ((1 / α ^ 2 : ℝ) : ℂ) * n ^ 2 + 2 * π * ((x / α ^ 2 : ℝ) : ℂ) * n) := by
    rw [ofReal_tsum, ← tsum_mul_left]
    congr 1; funext j
    rw [ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  -- the factor 1 / a^(1/2) equals α
  have hroot : (1 : ℂ) / ((1 / α ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = α := by
    have : ((1 / α ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((α⁻¹ : ℝ) : ℂ) := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_cpow (by positivity)]
      congr 1
      rw [show (1 / α ^ 2 : ℝ) = (α⁻¹) ^ (2 : ℝ) by rw [Real.rpow_two]; field_simp,
        ← Real.rpow_mul (by positivity)]
      norm_num
    rw [this]; push_cast; field_simp
  have hα0 : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  rw [hL, h, hroot, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  congr 1; funext n
  simp only [jacobiTheta₂_term]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  field_simp
  ring_nf
  simp only [I_sq]
  ring

/-- The shifted Gaussian sum is largest at shift `0`. -/
lemma gauss_shift_le (α : ℝ) (hα : 0 < α) (x : ℝ) :
    ∑' j : ℤ, rexp (-π * ((j : ℝ) - x) ^ 2 / α ^ 2) ≤ ∑' j : ℤ, rexp (-π * (j : ℝ) ^ 2 / α ^ 2) := by
  have hτ : 0 < (I * (α : ℂ) ^ 2).im := by
    simp only [mul_im, I_re, I_im, zero_mul, one_mul, zero_add]
    rw [← ofReal_pow, ofReal_re]; positivity
  have hs : Summable fun n : ℤ => ‖jacobiTheta₂_term n (-x) (I * (α : ℂ) ^ 2)‖ :=
    ((summable_jacobiTheta₂_term_iff _ _).2 hτ).norm
  have hnorm : ∀ (z : ℝ) (n : ℤ), ‖jacobiTheta₂_term n z (I * (α : ℂ) ^ 2)‖ =
      rexp (-π * n ^ 2 * α ^ 2) := by
    intro z n
    rw [norm_jacobiTheta₂_term]
    congr 1
    simp only [mul_im, I_re, I_im, zero_mul, one_mul, zero_add, ofReal_im, mul_zero, sub_zero]
    rw [← ofReal_pow, ofReal_re]
  -- value at 0 is α · Σ exp(-π n² α²)
  have h0 : ∑' j : ℤ, rexp (-π * (j : ℝ) ^ 2 / α ^ 2) = α * ∑' n : ℤ, rexp (-π * n ^ 2 * α ^ 2) := by
    have := gauss_shift_eq α hα 0
    simp only [sub_zero, neg_zero, ofReal_zero] at this
    apply ofReal_injective
    rw [this]
    push_cast
    congr 1
    congr 1; funext n
    simp only [jacobiTheta₂_term, mul_zero, zero_add]
    congr 1; ring_nf; simp only [I_sq]; ring
  have hx := gauss_shift_eq α hα x
  calc ∑' j : ℤ, rexp (-π * ((j : ℝ) - x) ^ 2 / α ^ 2)
      ≤ ‖((∑' j : ℤ, rexp (-π * ((j : ℝ) - x) ^ 2 / α ^ 2) : ℝ) : ℂ)‖ := by
        rw [norm_real, Real.norm_eq_abs]; exact le_abs_self _
    _ = α * ‖∑' n : ℤ, jacobiTheta₂_term n (-x) (I * (α : ℂ) ^ 2)‖ := by
        rw [hx, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hα]
    _ ≤ α * ∑' n : ℤ, ‖jacobiTheta₂_term n (-x) (I * (α : ℂ) ^ 2)‖ := by
        gcongr; exact norm_tsum_le_tsum_norm hs
    _ = _ := by
        rw [h0]; congr 1; congr 1; funext n
        have := hnorm (-x) n
        simpa using this

/-- `∑_{j ∈ ℤ} exp(-π j² / α²) < 1 + α` for `α > 0`. -/
lemma gauss_sum_lt (α : ℝ) (hα : 0 < α) :
    ∑' j : ℤ, rexp (-π * (j : ℝ) ^ 2 / α ^ 2) < 1 + α := by
  set b : ℝ := π / α ^ 2 with hb_def
  have hb : 0 < b := by positivity
  set g : ℝ → ℝ := fun y => rexp (-b * y ^ 2) with hg_def
  have hg_eq : ∀ y : ℝ, rexp (-π * y ^ 2 / α ^ 2) = g y := by
    intro y; simp only [hg_def, hb_def]; congr 1; field_simp
  have hg_pos : ∀ y, 0 < g y := fun y => Real.exp_pos _
  have hg_int : Integrable g := integrable_exp_neg_mul_sq hb
  have hg_anti : AntitoneOn g (Ici 0) := by
    intro x hx y hy hxy
    simp only [hg_def]
    apply Real.exp_le_exp.2
    have : x ^ 2 ≤ y ^ 2 := by
      have := mem_Ici.1 hx; nlinarith
    nlinarith
  have hg_even : ∀ y, g (-y) = g y := by intro y; simp [hg_def]
  have hI0 : ∫ y in Ioi (0 : ℝ), g y = α / 2 := by
    simp only [hg_def]
    rw [integral_gaussian_Ioi, hb_def]
    congr 1
    rw [show π / (π / α ^ 2) = α ^ 2 by field_simp, Real.sqrt_sq hα.le]
  -- tail from n = 2 is bounded by the integral over (1, ∞)
  have htail_le : ∀ N : ℕ, ∑ n ∈ Finset.range N, g ((n : ℝ) + 2) ≤ ∫ y in Ioi (1 : ℝ), g y := by
    intro N
    have h := AntitoneOn.sum_Ico_le_integral (f := g) (a := 1) (b := N + 1)
      (hg_anti.mono (by intro y hy; exact le_trans (by norm_num) (mem_Icc.1 hy).1))
      hg_int.integrableOn (fun t _ => (hg_pos t).le)
    rw [Finset.sum_Ico_eq_sum_range] at h
    simpa [add_comm, add_left_comm, show (N + 1 - 1 : ℕ) = N by omega, add_assoc,
      show (1 : ℝ) + 1 = 2 by norm_num] using h
  have hsum2 : Summable fun n : ℕ => g ((n : ℝ) + 2) :=
    summable_of_sum_range_le (fun n => (hg_pos _).le) htail_le
  have htail : ∑' n : ℕ, g ((n : ℝ) + 2) ≤ ∫ y in Ioi (1 : ℝ), g y :=
    Real.tsum_le_of_sum_range_le (fun n => (hg_pos _).le) htail_le
  have hsum1 : Summable fun n : ℕ => g ((n : ℝ) + 1) := by
    rw [← summable_nat_add_iff 1]; simpa [add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] using hsum2
  -- strict: g 1 < ∫₀¹ g
  have hfirst : g 1 < ∫ y in (0 : ℝ)..1, g y := by
    have := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (f := fun _ => g 1) (g := g) (a := 0) (b := 1) (by norm_num) continuousOn_const
      (by simp only [hg_def]; fun_prop)
      (fun y hy => hg_anti (mem_Ici.2 (le_of_lt hy.1)) (mem_Ici.2 (by norm_num)) hy.2)
      ⟨0, by norm_num, by simp only [hg_def]; apply Real.exp_lt_exp.2; nlinarith⟩
    simpa using this
  have hsplit : ∫ y in Ioi (0 : ℝ), g y = (∫ y in (0 : ℝ)..1, g y) + ∫ y in Ioi (1 : ℝ), g y := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← setIntegral_union (Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi hg_int.integrableOn hg_int.integrableOn, Ioc_union_Ioi_eq_Ioi zero_le_one]
  have hT : ∑' n : ℕ, g ((n : ℝ) + 1) < α / 2 := by
    rw [hsum1.tsum_eq_zero_add]
    have : ∑' n : ℕ, g (((n + 1 : ℕ) : ℝ) + 1) = ∑' n : ℕ, g ((n : ℝ) + 2) := by
      congr 1; funext n; push_cast; ring_nf
    rw [this, ← hI0, hsplit]
    simp only [Nat.cast_zero, zero_add]
    linarith
  -- assemble the sum over ℤ
  have hnat : Summable fun n : ℕ => g (n : ℝ) := by
    rw [← summable_nat_add_iff 1]; simpa using hsum1
  have hfun : (fun n : ℕ => g (((-(n + 1 : ℤ)) : ℤ) : ℝ)) = fun n : ℕ => g ((n : ℝ) + 1) := by
    funext n
    rw [← hg_even ((n : ℝ) + 1)]
    congr 1; push_cast; ring
  have hneg : Summable fun n : ℕ => g (((-(n + 1 : ℤ)) : ℤ) : ℝ) := by rw [hfun]; exact hsum1
  have hZ : ∑' j : ℤ, g (j : ℝ) = 1 + 2 * ∑' n : ℕ, g ((n : ℝ) + 1) := by
    rw [tsum_of_nat_of_neg_add_one (f := fun j : ℤ => g (j : ℝ)) (by simpa using hnat) hneg]
    simp only [Int.cast_natCast]
    rw [hfun, hnat.tsum_eq_zero_add]
    have h0 : g ((0 : ℕ) : ℝ) = 1 := by simp [hg_def]
    simp only [Nat.cast_add, Nat.cast_one] at *
    rw [h0]; ring
  calc ∑' j : ℤ, rexp (-π * (j : ℝ) ^ 2 / α ^ 2) = ∑' j : ℤ, g (j : ℝ) := by
        congr 1; funext j; exact hg_eq _
    _ = 1 + 2 * ∑' n : ℕ, g ((n : ℝ) + 1) := hZ
    _ < 1 + α := by linarith

/-- Shifted Gaussians are summable over `ℤ`. -/
lemma gauss_summable (α : ℝ) (hα : 0 < α) (x : ℝ) :
    Summable fun j : ℤ => rexp (-π * ((j : ℝ) - x) ^ 2 / α ^ 2) := by
  have hτ : 0 < (I * ((1 / α ^ 2 : ℝ) : ℂ)).im := by
    simp only [mul_im, I_re, I_im, zero_mul, one_mul, zero_add, ofReal_re]; positivity
  have hs := ((summable_jacobiTheta₂_term_iff (((-x / α ^ 2 : ℝ) : ℂ) * I) _).2 hτ).norm
  refine (hs.mul_left (rexp (-π * x ^ 2 / α ^ 2))).congr fun n => ?_
  rw [norm_jacobiTheta₂_term, ← Real.exp_add]
  congr 1
  simp only [mul_im, I_re, I_im, one_mul, zero_add, ofReal_re, ofReal_im, mul_zero, mul_one]
  field_simp
  ring

/-- The bijection `ℤ/sℤ × ℤ ≃ ℤ`, `(r, m) ↦ r + m s`. -/
noncomputable def resEquiv (s : ℕ) [NeZero s] : ZMod s × ℤ ≃ ℤ :=
  Equiv.ofBijective (fun p => (p.1.val : ℤ) + p.2 * s) <| by
    constructor
    · rintro ⟨r, m⟩ ⟨r', m'⟩ h
      simp only at h
      have hr : r = r' := by
        have := congrArg (fun z : ℤ => (z : ZMod s)) h
        simpa using this
      subst hr
      have hs : (s : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne s
      have : m * s = m' * s := by linarith
      simp only [Prod.mk.injEq, true_and]
      exact mul_right_cancel₀ hs this
    · intro j
      refine ⟨((j : ZMod s), j / s), ?_⟩
      simp only
      rw [ZMod.val_intCast]
      have := Int.emod_add_mul_ediv j s
      linarith [mul_comm (j / (s : ℤ)) (s : ℤ)]

/-- Regrouping a sum over `ℤ` by residue classes mod `s`. -/
lemma sum_residues (s : ℕ) [NeZero s] (h : ℤ → ℝ) (hs : Summable h) :
    ∑ r : ZMod s, ∑' m : ℤ, h ((r.val : ℤ) + m * s) = ∑' j : ℤ, h j := by
  rw [← (resEquiv s).tsum_eq]
  have hsp : Summable (h ∘ resEquiv s) := (resEquiv s).summable_iff.2 hs
  rw [show (∑' c : ZMod s × ℤ, h (resEquiv s c)) = ∑' c, (h ∘ resEquiv s) c from rfl,
    hsp.tsum_prod, tsum_fintype]
  rfl

end IntMulLemma45

open IntMulLemma45 in
theorem solution (s t : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hcop : Nat.Coprime s t)
    (α : ℝ) (hα : 0 < α) :
    ‖resS s t α‖ < 1 + α⁻¹ := by
  set M : ℝ := α⁻¹ * ∑' j : ℤ, rexp (-π * (j : ℝ) ^ 2 / α ^ 2) with hM_def
  have hM : M < 1 + α⁻¹ := by
    calc M < α⁻¹ * (1 + α) := mul_lt_mul_of_pos_left (gauss_sum_lt α hα) (inv_pos.2 hα)
      _ = 1 + α⁻¹ := by field_simp; ring
  have hM0 : 0 ≤ M := mul_nonneg (inv_nonneg.2 hα.le) (tsum_nonneg fun _ => (Real.exp_pos _).le)
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne s
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne t
  -- the kernel of 𝓢 in row k, as a function of the integer column index j
  set hk : ZMod t → ℤ → ℝ := fun k j =>
    α⁻¹ * Real.exp (-π * α⁻¹ ^ 2 * (s : ℝ) ^ 2 * (((k.val : ℕ) : ℝ) / t - (j : ℝ) / s) ^ 2)
    with hk_def
  have hk_eq : ∀ k j, hk k j =
      α⁻¹ * rexp (-π * ((j : ℝ) - (s : ℝ) * ((k.val : ℕ) : ℝ) / t) ^ 2 / α ^ 2) := by
    intro k j; simp only [hk_def]; congr 2; field_simp; ring
  have hk_sum : ∀ k, Summable (hk k) := by
    intro k
    rw [show hk k = fun j : ℤ =>
        α⁻¹ * rexp (-π * ((j : ℝ) - (s : ℝ) * ((k.val : ℕ) : ℝ) / t) ^ 2 / α ^ 2) from
      funext (hk_eq k)]
    exact (gauss_summable α hα _).mul_left _
  have hk_nonneg : ∀ k j, 0 ≤ hk k j := fun k j =>
    mul_nonneg (inv_nonneg.2 hα.le) (Real.exp_pos _).le
  -- each row sum of |𝓢| is at most M
  have hrow : ∀ k : ZMod t, ∑ r : ZMod s, ∑' m : ℤ, hk k ((r.val : ℤ) + m * s) ≤ M := by
    intro k
    rw [sum_residues s (hk k) (hk_sum k)]
    simp_rw [hk_eq]
    rw [tsum_mul_left, hM_def]
    exact mul_le_mul_of_nonneg_left (gauss_shift_le α hα _) (inv_nonneg.2 hα.le)
  refine lt_of_le_of_lt ?_ hM
  refine ContinuousLinearMap.opNorm_le_bound _ hM0 fun u => ?_
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hM0 (norm_nonneg u))]
  intro k
  simp only [resS, toCLM, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct, latticeMatrix, Matrix.of_apply]
  calc ‖∑ r : ZMod s, ((∑' m : ℤ, hk k ((r.val : ℤ) + m * s) : ℝ) : ℂ) * u r‖
      ≤ ∑ r : ZMod s, ‖((∑' m : ℤ, hk k ((r.val : ℤ) + m * s) : ℝ) : ℂ) * u r‖ := norm_sum_le _ _
    _ ≤ ∑ r : ZMod s, (∑' m : ℤ, hk k ((r.val : ℤ) + m * s)) * ‖u‖ := by
        gcongr with r
        rw [norm_mul, norm_real, Real.norm_eq_abs,
          abs_of_nonneg (tsum_nonneg fun m => hk_nonneg k _)]
        gcongr
        exact norm_le_pi_norm u r
    _ = (∑ r : ZMod s, ∑' m : ℤ, hk k ((r.val : ℤ) + m * s)) * ‖u‖ := by rw [Finset.sum_mul]
    _ ≤ M * ‖u‖ := by gcongr; exact hrow k
