-- Prove2me | solution 1 for IntMul.HvdH.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @avi
-- created : 2026-10-08T23:31:40.401924+00:00
-- url     : https://prove2.me/submissions/1229bf8a-3909-4fc4-8b0e-928d2436d70b

import Mathlib
import Definitions.Def_IntMul_HvdH_Resampling

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
theorem solution (s t : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hcop : Nat.Coprime s t)
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
