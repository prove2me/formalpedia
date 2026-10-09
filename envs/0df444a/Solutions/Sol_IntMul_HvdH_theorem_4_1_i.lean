-- Prove2me | solution 1 for IntMul.HvdH.theorem_4_1_i
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T11:45:47.683143+00:00
-- url     : https://prove2.me/submissions/360ec303-bb8a-4b88-bd73-ad8922c71a82

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import Definitions.Def_IntMul_HvdH_Resampling
import Definitions.Def_IntMul_HvdH_Tensor

/-!
Direct proof of IntMul.HvdH.theorem_4_1_i.

The proofs of Theorem 4.2 and Lemmas 4.5 and 4.6 are adapted from avi's
accepted Prove2Me submissions, respectively:
  1229bf8a-3909-4fc4-8b0e-928d2436d70b
  b7bc5cea-f9f6-4417-b76b-0f6b84f6f237
  f7841614-857e-4f2c-af79-cca60f0429b7
Public Prove2Me contributions are licensed under Apache 2.0.
The inverse construction, contraction bounds, and tensor assembly are proved below.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.unusedVariables false



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
theorem gaussian_resampling_norm (s t : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hcop : Nat.Coprime s t)
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


open Real IntMul.HvdH

namespace IntMulLemma46

lemma beta_abs (s t : ℕ) (j : ℤ) : |beta s t j| ≤ 1 / 2 := by
  unfold beta nearest
  set x : ℝ := (t : ℝ) * j / s
  have h1 := Int.floor_le (x + 1 / 2)
  have h2 := Int.lt_floor_add_one (x + 1 / 2)
  rw [abs_le]; constructor <;> linarith

lemma beta_periodic (s t : ℕ) (hs : (s : ℝ) ≠ 0) (j m : ℤ) :
    beta s t (j + m * s) = beta s t j := by
  unfold beta nearest
  have : (t : ℝ) * ((j + m * s : ℤ) : ℝ) / s = (t : ℝ) * j / s + ((m * t : ℤ) : ℝ) := by
    push_cast; field_simp
  rw [this, show (t : ℝ) * j / s + ((m * t : ℤ) : ℝ) + 1 / 2 = ((t : ℝ) * j / s + 1 / 2) + ((m * t : ℤ) : ℝ)
    by ring, Int.floor_add_intCast]
  push_cast; ring

/-- The exponent estimate of Lemma 4.6: for `h ≠ 0`,
`(ρh + β)² - β'² ≥ 2(ρ - 1)(|h| - 1/2)²` when `ρ ≥ 1` and `|β|, |β'| ≤ 1/2`. -/
lemma expo_bound (ρ β β' : ℝ) (hρ : 1 ≤ ρ) (hβ : |β| ≤ 1 / 2) (hβ' : |β'| ≤ 1 / 2)
    (h : ℤ) (hh : h ≠ 0) :
    2 * (ρ - 1) * (|(h : ℝ)| - 1 / 2) ^ 2 ≤ (ρ * h + β) ^ 2 - β' ^ 2 := by
  have habs : (1 : ℝ) ≤ |(h : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hh
  have hlow : ρ * (|(h : ℝ)| - 1 / 2) ≤ |ρ * h + β| := by
    have : |ρ * (h : ℝ)| - |β| ≤ |ρ * h + β| := by
      have := abs_sub_abs_le_abs_sub (ρ * (h : ℝ)) (-β); simpa [sub_neg_eq_add, abs_neg] using this
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < ρ)] at this
    nlinarith
  have hnn : 0 ≤ ρ * (|(h : ℝ)| - 1 / 2) := by nlinarith
  have hsq : (ρ * (|(h : ℝ)| - 1 / 2)) ^ 2 ≤ (ρ * h + β) ^ 2 := by
    rw [← sq_abs (ρ * h + β)]; exact pow_le_pow_left₀ hnn hlow 2
  have hβ'2 : β' ^ 2 ≤ 1 / 4 := by
    have := sq_abs β'; nlinarith [abs_nonneg β']
  have hq : 1 / 4 ≤ (|(h : ℝ)| - 1 / 2) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (ρ - 1)]

/-- `(n + 1/2)² ≥ 1/4 + 2n` for natural `n`. -/
lemma half_sq (n : ℕ) : 1 / 4 + 2 * (n : ℝ) ≤ ((n : ℝ) + 1 / 2) ^ 2 := by
  have : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ n := by exact_mod_cast h
      nlinarith
  nlinarith

/-- `2.01 e^{-πx/2} < 2^{-x}` for `x ≥ 1`. -/
lemma second_ineq (x : ℝ) (hx : 1 ≤ x) : 2.01 * rexp (-π * x / 2) < (2 : ℝ) ^ (-x) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpi := Real.pi_gt_three
  have hl2 := Real.log_two_lt_d9
  set y : ℝ := x * (π / 2 - Real.log 2)
  have hy : 0.8 ≤ y := by
    have : (0.8 : ℝ) ≤ π / 2 - Real.log 2 := by norm_num at hl2 ⊢; linarith
    calc (0.8 : ℝ) ≤ 1 * (π / 2 - Real.log 2) := by linarith
      _ ≤ x * (π / 2 - Real.log 2) := by apply mul_le_mul_of_nonneg_right hx; linarith
  have hey : (2.01 : ℝ) < rexp y := by
    have := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ y)
    nlinarith
  have : rexp (Real.log 2 * -x) = rexp (-π * x / 2) * rexp y := by
    rw [← Real.exp_add]; congr 1; simp only [y]; ring
  rw [this]
  have := Real.exp_pos (-π * x / 2)
  nlinarith

/-- `2 / (1 - e^{-2c}) < 2.01` once `c ≥ 6`. -/
lemma geom_factor (c : ℝ) (hc : 6 ≤ c) : 2 / (1 - rexp (-2 * c)) < 2.01 := by
  have h4 : (13 : ℝ) ≤ rexp 4 := by
    have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4); norm_num at this; linarith
  have h12 : (2197 : ℝ) ≤ rexp 12 := by
    have : rexp 12 = rexp 4 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have := pow_le_pow_left₀ (by norm_num) h4 3
    norm_num at this ⊢; linarith
  have hq : rexp (-2 * c) ≤ 1 / 2197 := by
    have : rexp (-2 * c) ≤ rexp (-12) := Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_neg] at this
    calc rexp (-2 * c) ≤ (rexp 12)⁻¹ := this
      _ ≤ 1 / 2197 := by rw [one_div]; exact inv_anti₀ (by norm_num) h12
  have hpos : 0 < 1 - rexp (-2 * c) := by linarith
  rw [div_lt_iff₀ hpos]; nlinarith

/-- The off-centre Gaussian tail used in Lemma 4.6. -/
noncomputable def tailFn (c : ℝ) (L : ℤ) (j : ℤ) : ℝ :=
  if j = L then 0 else rexp (-c * (|((j - L : ℤ) : ℝ)| - 1 / 2) ^ 2)

lemma tail_summable_and_le (c : ℝ) (hc : 0 < c) (L : ℤ) :
    Summable (tailFn c L) ∧ ∑' j, tailFn c L j ≤ 2 * rexp (-c / 4) / (1 - rexp (-2 * c)) := by
  set q : ℝ := rexp (-2 * c) with hq_def
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [hq_def, ← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  set φ : ℤ → ℝ := fun h => if h = 0 then 0 else rexp (-c * (|(h : ℝ)| - 1 / 2) ^ 2) with hφ
  have hshift : ∀ h : ℤ, tailFn c L (L + h) = φ h := by
    intro h; simp only [tailFn, hφ, add_sub_cancel_left, add_eq_left]
  have hφ0 : ∀ h, 0 ≤ φ h := by intro h; simp only [hφ]; split_ifs <;> positivity
  -- each half is dominated by e^{-c/4} q^n
  have hb : ∀ n : ℕ, rexp (-c * (((n : ℝ) + 1) - 1 / 2) ^ 2) ≤ rexp (-c / 4) * q ^ n := by
    intro n
    rw [hq_def, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have := half_sq n
    have e : ((n : ℝ) + 1) - 1 / 2 = (n : ℝ) + 1 / 2 := by ring
    rw [e]; nlinarith
  have hpos : ∀ n : ℕ, φ ((n : ℤ) + 1) = rexp (-c * (((n : ℝ) + 1) - 1 / 2) ^ 2) := by
    intro n
    simp only [hφ]
    rw [if_neg (by omega)]
    congr 3; push_cast; rw [abs_of_nonneg (by positivity)]
  have hneg : ∀ n : ℕ, φ (-((n : ℤ) + 1)) = rexp (-c * (((n : ℝ) + 1) - 1 / 2) ^ 2) := by
    intro n
    simp only [hφ]
    rw [if_neg (by omega)]
    congr 3; push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]
  have hgeo : Summable fun n : ℕ => rexp (-c / 4) * q ^ n :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hs1 : Summable fun n : ℕ => φ ((n : ℤ) + 1) :=
    Summable.of_nonneg_of_le (fun n => hφ0 _) (fun n => (hpos n).le.trans (hb n)) hgeo
  have hs2 : Summable fun n : ℕ => φ (-((n : ℤ) + 1)) :=
    Summable.of_nonneg_of_le (fun n => hφ0 _) (fun n => (hneg n).le.trans (hb n)) hgeo
  have hs0 : Summable fun n : ℕ => φ (n : ℤ) := by
    rw [← summable_nat_add_iff 1]; simpa using hs1
  have hsZ : Summable φ := Summable.of_nat_of_neg_add_one hs0 (by simpa using hs2)
  have hsum_geo : ∑' n : ℕ, rexp (-c / 4) * q ^ n = rexp (-c / 4) / (1 - q) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]; exact (div_eq_mul_inv _ _).symm
  have hT : ∑' h : ℤ, φ h ≤ 2 * rexp (-c / 4) / (1 - q) := by
    rw [tsum_of_nat_of_neg_add_one hs0 (by simpa using hs2), hs0.tsum_eq_zero_add]
    have e0 : φ ((0 : ℕ) : ℤ) = 0 := by simp [hφ]
    have h1 : ∑' n : ℕ, φ (((n + 1 : ℕ) : ℤ)) ≤ rexp (-c / 4) / (1 - q) := by
      rw [← hsum_geo]
      refine Summable.tsum_le_tsum (fun n => ?_) (by simpa using hs1) hgeo
      have := hpos n; push_cast at this ⊢; rw [this]; exact hb n
    have h2 : ∑' n : ℕ, φ (-((n : ℤ) + 1)) ≤ rexp (-c / 4) / (1 - q) := by
      rw [← hsum_geo]
      exact Summable.tsum_le_tsum (fun n => (hneg n).le.trans (hb n)) hs2 hgeo
    rw [e0]
    have : 2 * rexp (-c / 4) / (1 - q) = rexp (-c / 4) / (1 - q) + rexp (-c / 4) / (1 - q) := by ring
    linarith
  have hcomp : tailFn c L = φ ∘ (Equiv.subRight L) := by
    funext j
    simp only [Function.comp_apply, Equiv.subRight_apply]
    rw [← hshift (j - L), add_sub_cancel]
  refine ⟨?_, ?_⟩
  · rw [hcomp]; exact (Equiv.summable_iff (Equiv.subRight L)).2 hsZ
  · rw [hcomp]
    show ∑' j, φ (Equiv.subRight L j) ≤ _
    rw [Equiv.tsum_eq (Equiv.subRight L) φ]
    exact hT

/-- Regrouping a complex sum over `ℤ` by residue classes mod `s`. -/
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

lemma sum_residuesC (s : ℕ) [NeZero s] (h : ℤ → ℂ) (hs : Summable h) :
    ∑ r : ZMod s, ∑' m : ℤ, h ((r.val : ℤ) + m * s) = ∑' j : ℤ, h j := by
  rw [← (resEquiv s).tsum_eq]
  have hsp : Summable (h ∘ resEquiv s) := (resEquiv s).summable_iff.2 hs
  rw [show (∑' c : ZMod s × ℤ, h (resEquiv s c)) = ∑' c, (h ∘ resEquiv s) c from rfl,
    hsp.tsum_prod, tsum_fintype]
  rfl

end IntMulLemma46

open IntMulLemma46 Complex in
theorem gaussian_error_norm (s t : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hcop : Nat.Coprime s t)
    (α : ℝ) (hα : 0 < α) (hθ : 1 ≤ α ^ 2 * theta s t) :
    ‖errE s t α‖ < 2.01 * Real.exp (-π * α ^ 2 * theta s t / 2) ∧
      2.01 * Real.exp (-π * α ^ 2 * theta s t / 2) < (2 : ℝ) ^ (-(α ^ 2 * theta s t)) := by
  refine ⟨?_, ?_⟩
  swap
  · have := second_ineq (α ^ 2 * theta s t) hθ
    convert this using 3; ring
  have hspos : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have hs0 : (s : ℝ) ≠ 0 := hspos.ne'
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne t
  have hstR : (s : ℝ) < t := by exact_mod_cast hst
  set ρ : ℝ := (t : ℝ) / s with hρ_def
  have hρ : 1 ≤ ρ := (one_le_div hspos).2 hstR.le
  have hθρ : theta s t = ρ - 1 := rfl
  set c : ℝ := 2 * π * (α ^ 2 * theta s t) with hc_def
  have hc6 : 6 ≤ c := by
    have := Real.pi_gt_three
    rw [hc_def]; nlinarith
  have hc0 : 0 < c := by linarith
  set B : ℝ := 2 * rexp (-c / 4) / (1 - rexp (-2 * c)) with hB_def
  have hq1 : rexp (-2 * c) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  have hB0 : 0 ≤ B := by
    rw [hB_def]; exact div_nonneg (by positivity) (by linarith)
  have hB : B < 2.01 * rexp (-π * α ^ 2 * theta s t / 2) := by
    have h1 := geom_factor c hc6
    have hexp : rexp (-c / 4) = rexp (-π * α ^ 2 * theta s t / 2) := by
      congr 1; rw [hc_def]; ring
    rw [show B = 2 / (1 - rexp (-2 * c)) * rexp (-c / 4) by rw [hB_def]; ring, hexp]
    exact mul_lt_mul_of_pos_right h1 (Real.exp_pos _)
  refine lt_of_le_of_lt ?_ hB
  refine ContinuousLinearMap.opNorm_le_bound _ hB0 fun u => ?_
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hB0 (norm_nonneg u))]
  intro ℓ
  -- the row index ℓ and the selected row k = [tℓ/s] of 𝓣
  set L : ℤ := ((ℓ.val : ℕ) : ℤ) with hL_def
  have hL0 : (0 : ℝ) ≤ L := by rw [hL_def]; positivity
  have hLs : (L : ℝ) ≤ s - 1 := by
    have h : ℓ.val + 1 ≤ s := ZMod.val_lt ℓ
    have : ((ℓ.val : ℕ) : ℝ) + 1 ≤ s := by exact_mod_cast h
    rw [hL_def]; push_cast; linarith
  set k : ℤ := nearest ((t : ℝ) * ((ℓ.val : ℕ) : ℝ) / s) with hk_def
  have hk0 : 0 ≤ k := by
    rw [hk_def, nearest]; apply Int.floor_nonneg.2; positivity
  have hkt : k < t := by
    rw [hk_def, nearest, Int.floor_lt]
    have h1 : (t : ℝ) * ((ℓ.val : ℕ) : ℝ) / s ≤ (t : ℝ) * (s - 1) / s := by
      apply div_le_div_of_nonneg_right _ hspos.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa [hL_def] using hLs
    have h2 : (t : ℝ) * (s - 1) / s = t - ρ := by rw [hρ_def]; field_simp
    have h3 : (1 : ℝ) < ρ := (one_lt_div hspos).2 hstR
    push_cast; linarith
  have hkval : ((((k : ℤ) : ZMod t).val : ℕ) : ℝ) = (k : ℝ) := by
    have h := ZMod.val_intCast (n := t) k
    rw [Int.emod_eq_of_lt hk0 (by exact_mod_cast hkt)] at h
    exact_mod_cast h
  have hβL : beta s t L = (t : ℝ) * L / s - k := by
    simp only [beta, hk_def, hL_def, Int.cast_natCast]
  -- the coefficient of u_j in row ℓ of 𝓝u
  set a : ℤ → ℝ := fun j => rexp (-π * α ^ 2 * (t : ℝ) ^ 2 * ((k : ℝ) / t - (j : ℝ) / s) ^ 2) *
    rexp (π * α ^ 2 * beta s t j ^ 2) with ha_def
  have ha_alt : ∀ j : ℤ, a j =
      rexp (-(π * α ^ 2) * ((ρ * ((j - L : ℤ) : ℝ) + beta s t L) ^ 2 - beta s t j ^ 2)) := by
    intro j
    simp only [ha_def]
    rw [← Real.exp_add]
    congr 1
    rw [hβL, hρ_def]
    push_cast
    field_simp
    ring
  have haL : a L = 1 := by
    rw [ha_alt]; simp
  have ha_le : ∀ j, j ≠ L → a j ≤ rexp (-c * (|((j - L : ℤ) : ℝ)| - 1 / 2) ^ 2) := by
    intro j hj
    rw [ha_alt]
    apply Real.exp_le_exp.2
    have hx := expo_bound ρ (beta s t L) (beta s t j) hρ (beta_abs _ _ _) (beta_abs _ _ _)
      (j - L) (sub_ne_zero.2 hj)
    have hpa : 0 ≤ π * α ^ 2 := by positivity
    have : c = π * α ^ 2 * (2 * (ρ - 1)) := by rw [hc_def, hθρ]; ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hx hpa]
  have ha_nonneg : ∀ j, 0 ≤ a j := fun j => by rw [ha_def]; positivity
  have htail := tail_summable_and_le c hc0 L
  have ha_sum : Summable a := by
    refine Summable.of_nonneg_of_le ha_nonneg (fun j => ?_)
      (htail.1.add (hasSum_ite_eq L (1 : ℝ)).summable)
    by_cases hj : j = L
    · subst hj; simp [haL, tailFn]
    · have := ha_le j hj
      simp only [tailFn, if_neg hj]; simpa [hj] using this
  have hF : Summable fun j : ℤ => ((a j : ℝ) : ℂ) * u (j : ZMod s) := by
    refine Summable.of_norm_bounded (g := fun j => a j * ‖u‖) (ha_sum.mul_right _) fun j => ?_
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (ha_nonneg j)]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm u _) (ha_nonneg j)
  -- row ℓ of 𝓝u as one sum over ℤ
  have hN : (normN s t α u) ℓ = ∑' j : ℤ, ((a j : ℝ) : ℂ) * u (j : ZMod s) := by
    simp only [normN, ContinuousLinearMap.comp_apply, rowDel, resT, diagD, toCLM,
      LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, latticeMatrix, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.diagonal_apply,
      Finset.sum_ite_eq]
    rw [← sum_residuesC s _ hF]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [ofReal_tsum, ← tsum_mul_right]
    congr 1; funext m
    have hcast : ((((r.val : ℕ) : ℤ) + m * s : ℤ) : ZMod s) = r := by simp
    rw [hcast, ← hk_def, hkval]
    simp only [ha_def]
    rw [beta_periodic s t hs0 ((r.val : ℕ) : ℤ) m]
    push_cast
    ring
  have hrow : (errE s t α u) ℓ = ∑' j : ℤ, (if j = L then (0 : ℂ) else ((a j : ℝ) : ℂ) * u (j : ZMod s)) := by
    rw [errE, sub_apply, ContinuousLinearMap.id_apply, Pi.sub_apply, hN,
      hF.tsum_eq_add_tsum_ite L, haL]
    have : ((L : ℤ) : ZMod s) = ℓ := by rw [hL_def]; simp
    rw [this]
    simp
  rw [hrow]
  have hbound : ∀ j : ℤ, ‖(if j = L then (0 : ℂ) else ((a j : ℝ) : ℂ) * u (j : ZMod s))‖ ≤
      tailFn c L j * ‖u‖ := by
    intro j
    by_cases hj : j = L
    · simp [hj, tailFn]
    · simp only [if_neg hj, tailFn]
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (ha_nonneg j)]
      exact mul_le_mul (ha_le j hj) (norm_le_pi_norm u _) (norm_nonneg _) (by positivity)
  have hF2 : Summable fun j : ℤ => ‖(if j = L then (0 : ℂ) else ((a j : ℝ) : ℂ) * u (j : ZMod s))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound (htail.1.mul_right _)
  calc ‖∑' j : ℤ, (if j = L then (0 : ℂ) else ((a j : ℝ) : ℂ) * u (j : ZMod s))‖
      ≤ ∑' j : ℤ, ‖(if j = L then (0 : ℂ) else ((a j : ℝ) : ℂ) * u (j : ZMod s))‖ :=
        norm_tsum_le_tsum_norm hF2
    _ ≤ ∑' j : ℤ, tailFn c L j * ‖u‖ := Summable.tsum_le_tsum hbound hF2 (htail.1.mul_right _)
    _ = (∑' j : ℤ, tailFn c L j) * ‖u‖ := tsum_mul_right
    _ ≤ B * ‖u‖ := by gcongr; exact htail.2


open Complex Real IntMul.HvdH

namespace IntMulLemma42

/-- `e^{2πi z c / n}` depends only on the residue of the integer representative. -/
lemma char_val (n : ℕ) [NeZero n] (z : ZMod n) (x : ℤ) (hz : (x : ZMod n) = z) (c : ℤ) :
    cexp (2 * π * I * ((z.val : ℕ) : ℂ) * c / n) = cexp (2 * π * I * (x : ℂ) * c / n) := by
  obtain ⟨m, hm⟩ := (ZMod.intCast_eq_iff n x z).1 hz
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [hm]
  have : 2 * π * I * (((z.val : ℤ) + n * m : ℤ) : ℂ) * c / n =
      2 * π * I * ((z.val : ℕ) : ℂ) * c / n + ((m * c : ℤ) : ℂ) * (2 * π * I) := by
    push_cast; field_simp
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `e^{2πi m}` = 1 for integer `m`, in the form used below. -/
lemma cexp_int (m : ℤ) : cexp (2 * π * I * (m : ℂ)) = 1 := by
  rw [show 2 * π * I * (m : ℂ) = (m : ℂ) * (2 * π * I) by ring, Complex.exp_int_mul_two_pi_mul_I]

/-- The Poisson-summation core of Theorem 4.2. -/
lemma poisson_core (s t : ℕ) (hs : (0 : ℝ) < s) (ht : (0 : ℝ) < t) (α : ℝ) (hα : 0 < α)
    (k q : ℤ) :
    ∑' n : ℤ, cexp (-π * (α⁻¹ : ℂ) ^ 2 * (s : ℂ) ^ 2 * ((n : ℂ) / t - (q : ℂ) / s) ^ 2) *
        cexp (2 * π * I * (s : ℂ) * k * n / t) =
      ((α * t / s : ℝ) : ℂ) * ∑' N : ℤ, cexp (-π * (α : ℂ) ^ 2 * (t : ℂ) ^ 2 *
        ((k : ℂ) / t - (N : ℂ) / s) ^ 2) * cexp (-2 * π * I * (t : ℂ) * N * q / s) := by
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hα0 : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  set A : ℝ := ((s : ℝ) / (α * t)) ^ 2 with hA
  have hApos : 0 < A := by positivity
  have ha : 0 < ((A : ℝ) : ℂ).re := by rw [ofReal_re]; exact hApos
  set b : ℂ := ((α⁻¹ ^ 2 * s * q / t : ℝ) : ℂ) + I * ((s * k / t : ℝ) : ℂ) with hb
  have hP := Complex.tsum_exp_neg_quadratic ha b
  -- the factor 1 / A^(1/2) is α t / s
  have hroot : (1 : ℂ) / ((A : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((α * t / s : ℝ) : ℂ) := by
    have : ((A : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (((s : ℝ) / (α * t) : ℝ) : ℂ) := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hApos.le]
      congr 1
      rw [hA, ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
    rw [this]; push_cast; field_simp
  -- left side: each term is exp(-π A n² + 2π b n) times the constant exp(-π α⁻² q²)
  have hL : ∀ n : ℤ, cexp (-π * (α⁻¹ : ℂ) ^ 2 * (s : ℂ) ^ 2 * ((n : ℂ) / t - (q : ℂ) / s) ^ 2) *
        cexp (2 * π * I * (s : ℂ) * k * n / t) =
      cexp (-π * (α⁻¹ : ℂ) ^ 2 * (q : ℂ) ^ 2) *
        cexp (-π * ((A : ℝ) : ℂ) * n ^ 2 + 2 * π * b * n) := by
    intro n
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [hb, hA]; push_cast
    field_simp
    ring
  -- right side: each Poisson-dual term matches after cancelling exp(2πi k q) = 1
  have hR : ∀ N : ℤ, cexp (-π * (α⁻¹ : ℂ) ^ 2 * (q : ℂ) ^ 2) *
        cexp (-π / ((A : ℝ) : ℂ) * (N + I * b) ^ 2) =
      cexp (-π * (α : ℂ) ^ 2 * (t : ℂ) ^ 2 * ((k : ℂ) / t - (N : ℂ) / s) ^ 2) *
        cexp (-2 * π * I * (t : ℂ) * N * q / s) := by
    intro N
    rw [← Complex.exp_add, ← Complex.exp_add]
    have hkq := cexp_int (-(k * q))
    rw [← mul_one (cexp (_ + _)), ← hkq, ← Complex.exp_add]
    congr 1
    have h3 : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring
    have h4 : I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, I_sq]; norm_num
    rw [hb, hA]; push_cast
    field_simp
    ring_nf
    simp only [I_sq, h3, h4]
    ring
  calc ∑' n : ℤ, cexp (-π * (α⁻¹ : ℂ) ^ 2 * (s : ℂ) ^ 2 * ((n : ℂ) / t - (q : ℂ) / s) ^ 2) *
          cexp (2 * π * I * (s : ℂ) * k * n / t)
      = cexp (-π * (α⁻¹ : ℂ) ^ 2 * (q : ℂ) ^ 2) *
          ∑' n : ℤ, cexp (-π * ((A : ℝ) : ℂ) * n ^ 2 + 2 * π * b * n) := by
        rw [← tsum_mul_left]; congr 1; funext n; exact hL n
    _ = ((α * t / s : ℝ) : ℂ) * ∑' N : ℤ, cexp (-π * (α⁻¹ : ℂ) ^ 2 * (q : ℂ) ^ 2) *
          cexp (-π / ((A : ℝ) : ℂ) * (N + I * b) ^ 2) := by
        rw [hP, hroot, tsum_mul_left]; ring
    _ = _ := by congr 1; congr 1; funext N; exact hR N

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

/-- Regrouping a complex sum over `ℤ` by residue classes mod `s`. -/
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

lemma sum_residuesC (s : ℕ) [NeZero s] (h : ℤ → ℂ) (hs : Summable h) :
    ∑ r : ZMod s, ∑' m : ℤ, h ((r.val : ℤ) + m * s) = ∑' j : ℤ, h j := by
  rw [← (resEquiv s).tsum_eq]
  have hsp : Summable (h ∘ resEquiv s) := (resEquiv s).summable_iff.2 hs
  rw [show (∑' c : ZMod s × ℤ, h (resEquiv s c)) = ∑' c, (h ∘ resEquiv s) c from rfl,
    hsp.tsum_prod, tsum_fintype]
  rfl

/-- Norm of a real Gaussian factor times a unimodular character. -/
lemma norm_gauss_char (x y : ℝ) : ‖cexp (x : ℂ) * cexp ((y : ℂ) * I)‖ = rexp x := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_exp_ofReal]

lemma char_val_neg (n : ℕ) [NeZero n] (z : ZMod n) (x : ℤ) (hz : (x : ZMod n) = z) (c : ℤ) :
    cexp (-2 * π * I * ((z.val : ℕ) : ℂ) * c / n) = cexp (-2 * π * I * (x : ℂ) * c / n) := by
  have h := char_val n z x hz (-c)
  rw [show -2 * π * I * ((z.val : ℕ) : ℂ) * c / n = 2 * π * I * ((z.val : ℕ) : ℂ) * ((-c : ℤ) : ℂ) / n
    by push_cast; ring, h]
  congr 1; push_cast; ring

end IntMulLemma42

open IntMulLemma42 in
theorem gaussian_identity (s t : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hcop : Nat.Coprime s t)
    (α : ℝ) (hα : 0 < α) :
    (resT s t α).comp ((permS s t).comp (dft s)) =
      (permT s t).comp ((dft t).comp (resS s t α)) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have htR : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne t)
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hsR.ne'
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast htR.ne'
  have hα0 : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  ext u k
  simp only [ContinuousLinearMap.comp_apply, resT, resS, permS, permT, dft, toCLM,
    LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, LinearMap.funLeft_apply,
    Matrix.mulVec, dotProduct, Matrix.of_apply, latticeMatrix]
  -- both sides as ∑_q (coefficient) * u q
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  set K : ℤ := ((k.val : ℕ) : ℤ) with hK
  set Q : ℤ := ((q.val : ℕ) : ℤ) with hQ
  -- the common value: (1/s) ∑_N G(N) χ(N)
  set X : ℂ := ∑' N : ℤ, cexp (-π * (α : ℂ) ^ 2 * (t : ℂ) ^ 2 * ((K : ℂ) / t - (N : ℂ) / s) ^ 2) *
      cexp (-2 * π * I * (t : ℂ) * N * Q / s) with hX
  -- summability of the two families
  have hsumL : Summable fun N : ℤ => (1 / (s : ℂ)) * (cexp (-π * (α : ℂ) ^ 2 * (t : ℂ) ^ 2 *
      ((K : ℂ) / t - (N : ℂ) / s) ^ 2) * cexp (-2 * π * I * (t : ℂ) * N * Q / s)) * u q := by
    refine Summable.of_norm_bounded (g := fun N : ℤ => ‖(1 / (s : ℂ))‖ *
      rexp (-π * ((N : ℝ) - s * K / t) ^ 2 / (s / (α * t)) ^ 2) * ‖u q‖)
      (((gauss_summable _ (by positivity) _).mul_left _).mul_right _) fun N => ?_
    rw [norm_mul, norm_mul]
    gcongr
    have : cexp (-π * (α : ℂ) ^ 2 * (t : ℂ) ^ 2 * ((K : ℂ) / t - (N : ℂ) / s) ^ 2) *
        cexp (-2 * π * I * (t : ℂ) * N * Q / s) =
        cexp ((-π * ((N : ℝ) - s * K / t) ^ 2 / (s / (α * t)) ^ 2 : ℝ) : ℂ) *
          cexp (((-2 * π * t * N * Q / s : ℝ) : ℂ) * I) := by
      congr 1
      · congr 1; push_cast; field_simp; ring
      · congr 1; push_cast; ring
    rw [this, norm_gauss_char]
  -- left coefficient
  have hLcoef : ∑ r : ZMod s, ((∑' m : ℤ, rexp (-π * α ^ 2 * (t : ℝ) ^ 2 *
        (((k.val : ℕ) : ℝ) / t - (((r.val : ℕ) : ℤ) + m * s : ℤ) / s) ^ 2) : ℝ) : ℂ) *
        (1 / (s : ℂ) * cexp (-2 * π * I * ((((t : ZMod s) * r).val : ℕ) : ℂ) * ((q.val : ℕ) : ℂ) / s) *
          u q) = (1 / (s : ℂ)) * X * u q := by
    rw [hX, ← tsum_mul_left, ← tsum_mul_right, ← sum_residuesC s _ hsumL]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [ofReal_tsum, ← tsum_mul_right]
    congr 1; funext m
    have hz : ((t * (((r.val : ℕ) : ℤ) + m * s) : ℤ) : ZMod s) = (t : ZMod s) * r := by simp
    have hc := char_val_neg s ((t : ZMod s) * r) (t * (((r.val : ℕ) : ℤ) + m * s)) hz Q
    simp only [hK, hQ, Int.cast_natCast] at hc ⊢
    push_cast at hc ⊢
    rw [hc]
    ring_nf
  -- right coefficient
  set Ψ : ℤ → ℂ := fun n => cexp (-π * (α⁻¹ : ℂ) ^ 2 * (s : ℂ) ^ 2 * ((n : ℂ) / t - (Q : ℂ) / s) ^ 2) *
      cexp (2 * π * I * (s : ℂ) * K * n / t) with hΨ
  have hΨsum : Summable Ψ := by
    refine Summable.of_norm_bounded (g := fun n : ℤ =>
      rexp (-π * ((n : ℝ) - t * Q / s) ^ 2 / (α * t / s) ^ 2))
      (gauss_summable _ (by positivity) _) fun n => ?_
    have : Ψ n = cexp ((-π * ((n : ℝ) - t * Q / s) ^ 2 / (α * t / s) ^ 2 : ℝ) : ℂ) *
        cexp (((2 * π * s * K * n / t : ℝ) : ℂ) * I) := by
      simp only [hΨ]
      congr 1
      · congr 1; push_cast; field_simp
      · congr 1; push_cast; ring
    rw [this, norm_gauss_char]
  have hRcoef : ∑ ℓ : ZMod t, 1 / (t : ℂ) * cexp (-2 * π * I * (((-(s : ZMod t) * k).val : ℕ) : ℂ) *
        ((ℓ.val : ℕ) : ℂ) / t) * (((∑' m : ℤ, α⁻¹ * rexp (-π * α⁻¹ ^ 2 * (s : ℝ) ^ 2 *
          (((ℓ.val : ℕ) : ℝ) / t - (((q.val : ℕ) : ℤ) + m * s : ℤ) / s) ^ 2) : ℝ) : ℂ) * u q) =
      (1 / (t : ℂ)) * (α⁻¹ : ℂ) * (∑' n : ℤ, Ψ n) * u q := by
    have hneg : Summable fun n : ℤ => Ψ (-n) := (Equiv.neg ℤ).summable_iff.2 hΨsum
    rw [← sum_residuesC t Ψ hΨsum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [← (Equiv.neg ℤ).tsum_eq (fun m : ℤ => Ψ (((ℓ.val : ℕ) : ℤ) + m * t))]
    rw [ofReal_tsum, ← tsum_mul_right, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_right]
    congr 1; funext m
    have hz : ((-(s : ℤ) * K : ℤ) : ZMod t) = -(s : ZMod t) * k := by simp [hK]
    have hc := char_val_neg t (-(s : ZMod t) * k) (-(s : ℤ) * K) hz ((ℓ.val : ℕ) : ℤ)
    push_cast at hc ⊢
    rw [hc]
    simp only [hΨ, Equiv.neg_apply]
    have hχ : cexp (2 * π * I * (s : ℂ) * K * ((((ℓ.val : ℕ) : ℤ) + -m * (t : ℤ) : ℤ) : ℂ) / t) =
        cexp (-2 * π * I * (-(s : ℂ) * K) * ((ℓ.val : ℕ) : ℂ) / t) := by
      rw [← mul_one (cexp (-2 * π * I * (-(s : ℂ) * K) * ((ℓ.val : ℕ) : ℂ) / t)),
        ← cexp_int (-(s * K * m)), ← Complex.exp_add]
      congr 1; push_cast; field_simp
    have hG : cexp (-π * (α⁻¹ : ℂ) ^ 2 * (s : ℂ) ^ 2 *
          (((((ℓ.val : ℕ) : ℤ) + -m * (t : ℤ) : ℤ) : ℂ) / t - (Q : ℂ) / s) ^ 2) =
        cexp (-π * (α⁻¹ : ℂ) ^ 2 * (s : ℂ) ^ 2 *
          (((ℓ.val : ℕ) : ℂ) / t - (((q.val : ℕ) : ℂ) + (m : ℂ) * s) / s) ^ 2) := by
      congr 1; rw [hQ]; push_cast; field_simp; ring
    rw [hχ, hG]
    ring
  rw [hLcoef, hRcoef, poisson_core s t hsR htR α hα K Q, ← hX]
  push_cast
  field_simp



open scoped BigOperators
open IntMul.HvdH

namespace HvdHDirect

lemma diag_apply (s t : ℕ) [NeZero s] (a : ℝ) (u : ZMod s → ℂ) (j : ZMod s) :
    diagD s t a u j = (Real.exp (Real.pi * a ^ 2 * beta s t (j.val : ℕ) ^ 2) : ℂ) * u j := by
  simp [diagD, toCLM, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

lemma reindex_norm {m n : Type} [Fintype m] [Fintype n] (f : m → n) :
    ‖LinearMap.toContinuousLinearMap (LinearMap.funLeft ℂ ℂ f)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg u)]
  intro j
  exact norm_le_pi_norm u (f j)

lemma one_dim (p s t a : ℕ) [NeZero s] [NeZero t]
    (hst : s < t) (hcop : Nat.Coprime s t) (ha : 2 ≤ a)
    (hap : (a : ℝ) < Real.sqrt p) (htheta : (p : ℝ) / a ^ 4 ≤ theta s t) :
    ∃ A : (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ),
    ∃ B : (ZMod t → ℂ) →L[ℂ] (ZMod s → ℂ),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
        dft s = ((2 : ℂ) ^ (2 * a ^ 2)) • (B.comp ((dft t).comp A)) := by
  classical
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := by linarith
  have ha2 : (0 : ℝ) < (a : ℝ) ^ 2 := pow_pos ha0 2
  have ha4 : (0 : ℝ) < (a : ℝ) ^ 4 := pow_pos ha0 4
  have hpa : (a : ℝ) ^ 2 < p := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ p by positivity), Real.sqrt_nonneg (p : ℝ)]
  have hx : 1 ≤ (a : ℝ) ^ 2 * theta s t := by
    have hh := (div_le_iff₀ ha4).1 htheta
    have hmul : (p : ℝ) ≤ (a : ℝ) ^ 2 * ((a : ℝ) ^ 2 * theta s t) := by
      nlinarith only [hh]
    by_contra h
    have hlt : (a : ℝ) ^ 2 * ((a : ℝ) ^ 2 * theta s t) < (a : ℝ) ^ 2 := by
      nlinarith [lt_of_not_ge h]
    linarith
  have hE : ‖errE s t (a : ℝ)‖ < 1 / 2 := by
    have hh := gaussian_error_norm s t hst hcop (a : ℝ) ha0 hx
    apply (hh.1.trans hh.2).trans_le
    calc (2 : ℝ) ^ (-((a : ℝ) ^ 2 * theta s t)) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 / 2 := by norm_num
  let E := errE s t (a : ℝ)
  let J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) := ∑' n : ℕ, (-E) ^ n
  have hsmall : ‖-E‖ < 1 := by simpa only [norm_neg] using hE.trans (by norm_num)
  have hN : normN s t (a : ℝ) = 1 - (-E) := by
    change normN s t (a : ℝ) = 1 - (-(normN s t (a : ℝ) - 1))
    abel
  have hJN : J * normN s t (a : ℝ) = 1 := by
    rw [hN]
    exact geom_series_mul_neg (-E) hsmall
  have hNJ : normN s t (a : ℝ) * J = 1 := by
    rw [hN]
    exact mul_neg_geom_series (-E) hsmall
  have hJnorm : ‖J‖ ≤ 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro u
    have hid : J u = u - E (J u) := by
      have h := congrArg (fun F : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) => F u) hNJ
      change normN s t (a : ℝ) (J u) = u at h
      have : normN s t (a : ℝ) (J u) = J u + E (J u) := by
        simp [E, errE]
      rw [this] at h
      exact eq_sub_of_add_eq h
    have hb := norm_sub_le u (E (J u))
    have hb' := E.le_opNorm (J u)
    rw [← hid] at hb
    have hn : 0 ≤ ‖J u‖ := norm_nonneg _
    have he : ‖E‖ ≤ 1 / 2 := hE.le
    nlinarith
  have hDnorm : ‖diagD s t (a : ℝ)‖ ≤ Real.exp (Real.pi * (a : ℝ) ^ 2 / 4) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
    intro u
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro j
    rw [diag_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul _ (norm_le_pi_norm u j) (norm_nonneg _) (Real.exp_pos _).le
    apply Real.exp_le_exp.2
    have hb := IntMulLemma46.beta_abs s t (j.val : ℕ)
    have hb2 : beta s t (j.val : ℕ) ^ 2 ≤ 1 / 4 := by
      rw [abs_le] at hb
      nlinarith
    nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg (a : ℝ)),
      mul_le_mul_of_nonneg_left hb2 (mul_nonneg Real.pi_pos.le (sq_nonneg (a : ℝ)))]
  have hDsurj : Function.Surjective (diagD s t (a : ℝ)) := by
    intro u
    refine ⟨fun j => u j / (Real.exp (Real.pi * (a : ℝ) ^ 2 * beta s t (j.val : ℕ) ^ 2) : ℂ), ?_⟩
    funext j
    rw [diag_apply]
    have hz : (Real.exp (Real.pi * (a : ℝ) ^ 2 * beta s t (j.val : ℕ) ^ 2) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.exp_pos _).ne'
    field_simp
  have hleft (u : ZMod s → ℂ) :
      diagD s t (a : ℝ) (J (rowDel s t (resT s t (a : ℝ) u))) = u := by
    obtain ⟨v, rfl⟩ := hDsurj u
    have hid := congrArg (fun F : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) => F v) hJN
    change J (normN s t (a : ℝ) v) = v at hid
    change diagD s t (a : ℝ) (J (normN s t (a : ℝ) v)) = diagD s t (a : ℝ) v
    rw [hid]
  obtain ⟨v, hv⟩ := (ZMod.isUnit_iff_coprime t s).2 hcop.symm
  let P : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) :=
    LinearMap.toContinuousLinearMap (LinearMap.funLeft ℂ ℂ fun j : ZMod s => (↑v⁻¹ : ZMod s) * j)
  have hPnorm : ‖P‖ ≤ 1 := reindex_norm _
  have hPP (u : ZMod s → ℂ) : P (permS s t u) = u := by
    funext j
    change u ((t : ZMod s) * ((↑v⁻¹ : ZMod s) * j)) = u j
    simp [← hv, ← mul_assoc]
  have hCnorm : ‖rowDel s t‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro u
    rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg u)]
    intro j
    simp only [rowDel, toCLM, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Matrix.of_apply]
    simpa using norm_le_pi_norm u ((nearest ((t : ℝ) * (j.val : ℕ) / s) : ℤ) : ZMod t)
  have hPtnorm : ‖permT s t‖ ≤ 1 := reindex_norm _
  let B0 := P.comp ((diagD s t (a : ℝ)).comp (J.comp ((rowDel s t).comp (permT s t))))
  have hB0norm : ‖B0‖ ≤ Real.exp (Real.pi * (a : ℝ) ^ 2 / 4) * 2 := by
    calc ‖B0‖ ≤ ‖P‖ * (‖diagD s t (a : ℝ)‖ * (‖J‖ * (‖rowDel s t‖ * ‖permT s t‖))) := by
          dsimp [B0]
          refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg P)
          refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg (diagD s t (a : ℝ)))
          refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg J)
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (Real.exp (Real.pi * (a : ℝ) ^ 2 / 4) * (2 * (1 * 1))) := by
          gcongr
      _ = Real.exp (Real.pi * (a : ℝ) ^ 2 / 4) * 2 := by ring
  have hfactor (u : ZMod s → ℂ) : B0 (dft t (resS s t (a : ℝ) u)) = dft s u := by
    have hid := congrArg (fun F => F u) (gaussian_identity s t hst hcop (a : ℝ) ha0)
    simp only [ContinuousLinearMap.comp_apply] at hid
    change P (diagD s t (a : ℝ) (J (rowDel s t (permT s t (dft t (resS s t (a : ℝ) u)))))) = _
    rw [← hid, hleft, hPP]
  let k := 2 * a ^ 2
  have hscale : 4 * Real.exp (Real.pi * (a : ℝ) ^ 2 / 4) ≤ (2 : ℝ) ^ k := by
    have hpow : (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
      congr 1; ring
    have ha_sq : 4 ≤ (a : ℝ) ^ 2 := by nlinarith
    have he : Real.pi * (a : ℝ) ^ 2 / 4 + 2 * Real.log 2 ≤ (k : ℝ) * Real.log 2 := by
      dsimp [k]
      push_cast
      nlinarith [Real.pi_lt_d2, Real.log_two_gt_d9, Real.log_two_lt_d9]
    rw [hpow]
    have hfour : (4 : ℝ) = Real.exp (2 * Real.log 2) := by
      rw [show 2 * Real.log 2 = Real.log 2 + Real.log 2 by ring,
        Real.exp_add, Real.exp_log (by norm_num)]
      norm_num
    calc 4 * Real.exp (Real.pi * (a : ℝ) ^ 2 / 4) =
          Real.exp (2 * Real.log 2 + Real.pi * (a : ℝ) ^ 2 / 4) := by
            conv_lhs => lhs; rw [hfour]
            rw [Real.exp_add]
      _ ≤ Real.exp ((k : ℝ) * Real.log 2) := Real.exp_le_exp.2 (by linarith)
  let A := (1 / 2 : ℂ) • resS s t (a : ℝ)
  let B := ((2 : ℂ) / (2 : ℂ) ^ k) • B0
  refine ⟨A, B, ?_, ?_, ?_⟩
  · have hsN := gaussian_resampling_norm s t hst hcop (a : ℝ) ha0
    have hainv : (a : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ ha0).2 (by linarith)
    dsimp [A]
    rw [norm_smul]
    norm_num
    nlinarith
  · dsimp [B]
    rw [norm_smul, norm_div, norm_pow]
    norm_num
    have hkpos : (0 : ℝ) < 2 ^ k := by positivity
    calc (2 / 2 ^ k) * ‖B0‖ ≤ (2 / 2 ^ k) * (Real.exp (Real.pi * (a : ℝ) ^ 2 / 4) * 2) := by gcongr
      _ = (4 * Real.exp (Real.pi * (a : ℝ) ^ 2 / 4)) / 2 ^ k := by ring
      _ ≤ 1 := (div_le_one hkpos).2 hscale
  · ext u j
    have hc : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    have hscalar : (2 : ℂ) ^ k * ((2 : ℂ) / (2 : ℂ) ^ k * (1 / 2)) = 1 := by field_simp
    change dft s u j = (((2 : ℂ) ^ k) • (B (dft t (A u)))) j
    dsimp [A, B]
    simp only [smul_apply, map_smul, smul_smul]
    rw [hfactor]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp

end HvdHDirect



open scoped BigOperators
open IntMul.HvdH

namespace HvdHDirect

noncomputable def mat {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (f : (m → ℂ) →L[ℂ] (n → ℂ)) : Matrix n m ℂ := by
  classical
  exact LinearMap.toMatrix' f.toLinearMap

lemma mat_injective {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {f g : (m → ℂ) →L[ℂ] (n → ℂ)} (h : mat f = mat g) : f = g := by
  classical
  have hL : f.toLinearMap = g.toLinearMap := LinearMap.toMatrix'.injective h
  ext u j
  exact congrArg (fun L : (m → ℂ) →ₗ[ℂ] (n → ℂ) => L u j) hL

lemma mat_comp {m n r : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [Fintype r] [DecidableEq r]
    (g : (n → ℂ) →L[ℂ] (r → ℂ)) (f : (m → ℂ) →L[ℂ] (n → ℂ)) :
    mat (g.comp f) = mat g * mat f := by
  classical
  exact LinearMap.toMatrix'_comp g.toLinearMap f.toLinearMap

lemma mat_smul {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (c : ℂ) (f : (m → ℂ) →L[ℂ] (n → ℂ)) : mat (c • f) = c • mat f := by
  classical
  exact map_smul (LinearMap.toMatrix' : ((m → ℂ) →ₗ[ℂ] (n → ℂ)) ≃ₗ[ℂ] Matrix n m ℂ) c f.toLinearMap

noncomputable def tensorMatrix {ι : Type} [Fintype ι] [DecidableEq ι]
    {m n : ι → Type} (M : ∀ i, Matrix (n i) (m i) ℂ) :
    Matrix (∀ i, n i) (∀ i, m i) ℂ := fun j k => ∏ i, M i (j i) (k i)

noncomputable def tensor {ι : Type} [Fintype ι] [DecidableEq ι]
    {m n : ι → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (f : ∀ i, (m i → ℂ) →L[ℂ] (n i → ℂ)) :
    ((∀ i, m i) → ℂ) →L[ℂ] ((∀ i, n i) → ℂ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (tensorMatrix (fun i => mat (f i))))

lemma mat_tensor {ι : Type} [Fintype ι] [DecidableEq ι]
    {m n : ι → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (f : ∀ i, (m i → ℂ) →L[ℂ] (n i → ℂ)) :
    mat (tensor f) = tensorMatrix (fun i => mat (f i)) := by
  classical
  simp only [mat, tensor, LinearMap.coe_toContinuousLinearMap, LinearMap.toMatrix'_toLin']

lemma tensorMatrix_mul {ι : Type} [Fintype ι] [DecidableEq ι]
    {m n r : ι → Type} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (M : ∀ i, Matrix (r i) (n i) ℂ) (N : ∀ i, Matrix (n i) (m i) ℂ) :
    tensorMatrix (fun i => M i * N i) = tensorMatrix M * tensorMatrix N := by
  classical
  ext j k
  simp only [tensorMatrix, Matrix.mul_apply]
  simp_rw [← Finset.prod_mul_distrib]
  simpa only [Fintype.piFinset_univ] using
    (Finset.prod_univ_sum (fun i => (Finset.univ : Finset (n i)))
      (fun i x => M i (j i) x * N i x (k i)))

lemma tensor_comp {ι : Type} [Fintype ι] [DecidableEq ι]
    {m n r : ι → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] [∀ i, Fintype (r i)] [∀ i, DecidableEq (r i)]
    (g : ∀ i, (n i → ℂ) →L[ℂ] (r i → ℂ))
    (f : ∀ i, (m i → ℂ) →L[ℂ] (n i → ℂ)) :
    tensor (fun i => (g i).comp (f i)) = (tensor g).comp (tensor f) := by
  apply mat_injective
  rw [mat_comp, mat_tensor, mat_tensor, mat_tensor]
  simp_rw [mat_comp]
  exact tensorMatrix_mul _ _

lemma tensor_smul {ι : Type} [Fintype ι] [DecidableEq ι]
    {m n : ι → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (c : ℂ) (f : ∀ i, (m i → ℂ) →L[ℂ] (n i → ℂ)) :
    tensor (fun i => c • f i) = c ^ Fintype.card ι • tensor f := by
  classical
  apply mat_injective
  rw [mat_smul, mat_tensor, mat_tensor]
  ext j k
  simp [tensorMatrix, mat_smul, Finset.prod_mul_distrib]

open scoped Matrix.Norms.Operator

lemma matrix_row_bound {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (f : (m → ℂ) →L[ℂ] (n → ℂ)) (j : n) : ∑ k, ‖mat f j k‖ ≤ ‖f‖ := by
  classical
  have heq : ‖mat f‖ = ‖f‖ := Matrix.linfty_opNorm_toMatrix f
  rw [← heq, Matrix.linfty_opNorm_def]
  have h := (Finset.le_sup (f := fun i : n => ∑ k : m, ‖mat f i k‖₊) (Finset.mem_univ j))
  have h' := (NNReal.coe_le_coe).2 h
  simpa only [NNReal.coe_sum, coe_nnnorm] using h'

lemma tensor_norm {ι : Type} [Fintype ι] [DecidableEq ι]
    {m n : ι → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (f : ∀ i, (m i → ℂ) →L[ℂ] (n i → ℂ)) (hf : ∀ i, ‖f i‖ ≤ 1) :
    ‖tensor f‖ ≤ 1 := by
  classical
  have hr (j : ∀ i, n i) : ∑ k : ∀ i, m i, ∏ i, ‖mat (f i) (j i) (k i)‖ ≤ 1 := by
    have heq : (∑ k : ∀ i, m i, ∏ i, ‖mat (f i) (j i) (k i)‖) =
        ∏ i, ∑ k : m i, ‖mat (f i) (j i) k‖ := by
      symm
      simpa only [Fintype.piFinset_univ] using
        (Finset.prod_univ_sum (fun i => (Finset.univ : Finset (m i)))
          (fun i k => ‖mat (f i) (j i) k‖))
    rw [heq]
    exact Finset.prod_le_one (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (fun i _ => (matrix_row_bound (f i) (j i)).trans (hf i))
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg u)]
  intro j
  change ‖∑ k, tensorMatrix (fun i => mat (f i)) j k * u k‖ ≤ ‖u‖
  calc ‖∑ k, tensorMatrix (fun i => mat (f i)) j k * u k‖
      ≤ ∑ k, ‖tensorMatrix (fun i => mat (f i)) j k * u k‖ := norm_sum_le _ _
    _ ≤ ∑ k : ∀ i, m i, (∏ i, ‖mat (f i) (j i) (k i)‖) * ‖u‖ := by
        apply Finset.sum_le_sum
        intro k _
        simp only [norm_mul, tensorMatrix, norm_prod]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm u k) (by positivity)
    _ = (∑ k : ∀ i, m i, ∏ i, ‖mat (f i) (j i) (k i)‖) * ‖u‖ := by rw [Finset.sum_mul]
    _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right (hr j) (norm_nonneg u)
    _ = ‖u‖ := one_mul _

lemma tensor_dft {d : ℕ} (s : Fin d → ℕ) [∀ i, NeZero (s i)] :
    tensor (fun i => dft (s i)) = dftN s := by
  classical
  apply mat_injective
  rw [mat_tensor]
  simp only [dft, dftN, toCLM, mat, LinearMap.coe_toContinuousLinearMap,
    LinearMap.toMatrix'_toLin']
  rfl

end HvdHDirect

open HvdHDirect

theorem solution (d p : ℕ) (hd : 1 ≤ d) (hp : 100 ≤ p) (s t : Fin d → ℕ)
    [∀ i, NeZero (s i)] [∀ i, NeZero (t i)] (hs : ∀ i, 2 ≤ s i) (hst : ∀ i, s i < t i)
    (htp : ∀ i, t i < 2 ^ p) (hcop : ∀ i, Nat.Coprime (s i) (t i)) (a : ℕ) (ha : 2 ≤ a)
    (hap : (a : ℝ) < Real.sqrt p) (htheta : ∀ i, (p : ℝ) / a ^ 4 ≤ theta (s i) (t i)) :
    ∃ A : (TIdx s → ℂ) →L[ℂ] (TIdx t → ℂ), ∃ B : (TIdx t → ℂ) →L[ℂ] (TIdx s → ℂ),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
        dftN s = ((2 : ℂ) ^ (2 * d * a ^ 2)) • (B.comp ((dftN t).comp A)) := by
  classical
  have hi := fun i : Fin d => one_dim p (s i) (t i) a (hst i) (hcop i) ha hap (htheta i)
  choose A B hA hB hfactor using hi
  refine ⟨tensor A, tensor B, tensor_norm A hA, tensor_norm B hB, ?_⟩
  calc dftN s = tensor (fun i => dft (s i)) := (tensor_dft s).symm
    _ = tensor (fun i => (2 : ℂ) ^ (2 * a ^ 2) • ((B i).comp ((dft (t i)).comp (A i)))) := by
          congr 1
          funext i
          exact hfactor i
    _ = ((2 : ℂ) ^ (2 * a ^ 2)) ^ d •
          tensor (fun i => (B i).comp ((dft (t i)).comp (A i))) := by
          simpa using tensor_smul ((2 : ℂ) ^ (2 * a ^ 2))
            (fun i => (B i).comp ((dft (t i)).comp (A i)))
    _ = ((2 : ℂ) ^ (2 * a ^ 2)) ^ d • ((tensor B).comp ((dftN t).comp (tensor A))) := by
          rw [tensor_comp, tensor_comp, tensor_dft]
    _ = ((2 : ℂ) ^ (2 * d * a ^ 2)) • ((tensor B).comp ((dftN t).comp (tensor A))) := by
          rw [← pow_mul]
          congr 2
          ring


#print axioms solution
