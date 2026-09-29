-- Prove2me | solution 1 for LanglandsTunnell.Converse.GammaR_mul_integral_dualTorusTriple_detPow_colHarmonic_eq_mul_prod_GammaR_of_evenPrincipal_of_weightZeroProfile
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/05b8651d-1e59-5b2f-81e9-bbfd0d7fa373

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

import Mathlib
import Theorems.Thm_LanglandsTunnell_integral_prod_eq_setIntegral_Ioi_setIntegral_Ioi_sum_reflections
import Theorems.Thm_LanglandsTunnell_integral_mulConvGaussian_torusGauss_eq_GammaR_prod_div_of_balance
import Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_dualQuadruple_and_torusTriple_detPow_colHarmonic_of_evenSheet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_detPow_colHarmonic_eq_mul_prod_GammaR_of_evenPrincipal_of_weightZeroProfile

set_option autoImplicit false
set_option maxHeartbeats 4000000

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

namespace Eval00

theorem ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (z : ℂ) :
    ((x : ℝ) : ℂ) ^ z = Complex.exp (z * ((Real.log x : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hx.ne'), Complex.ofReal_log hx.le, mul_comm]

theorem ofReal_eq_exp_log {x : ℝ} (hx : 0 < x) : ((x : ℝ) : ℂ) = Complex.exp ((Real.log x : ℝ) : ℂ) := by
  rw [← Complex.ofReal_exp, Real.exp_log hx]

theorem quasiChar_of_pos (u : ℂ) (a : ZMod 2) {x : ℝ} (hx : 0 < x) : ArchR.quasiChar u a x = ((x : ℝ) : ℂ) ^ u := by
  unfold ArchR.quasiChar
  rw [abs_of_pos hx]
  split_ifs
  · rw [mul_one]
  · rw [sign_pos hx]; simp

theorem quasiChar_neg (u : ℂ) (a : ZMod 2) (x : ℝ) (hx : x ≠ 0) :
    ArchR.quasiChar u a (-x) = (-1 : ℂ) ^ a.val * ArchR.quasiChar u a x := by
  unfold ArchR.quasiChar
  rw [abs_neg]
  have ha : a = 0 ∨ a = 1 := (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a
  rcases ha with h | h
  · subst h; simp
  · subst h
    simp only [one_ne_zero, if_false, ZMod.val_one, pow_one, Left.sign_neg, SignType.coe_neg]
    push_cast
    ring

theorem quasiChar_zero_pos (a : ZMod 2) {x : ℝ} (hx : 0 < x) : ArchR.quasiChar 0 a x = 1 := by
  rw [quasiChar_of_pos _ _ hx, Complex.cpow_zero]

theorem v0 : (0 : ZMod 2).val = 0 := rfl
theorem v1 : (1 : ZMod 2).val = 1 := rfl

theorem ae_good3 : ∀ᵐ x : ℝ × ℝ × ℝ ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod
    ((volume : Measure ℝ).restrict (Set.Ioi 0)))), x.1 ≠ 0 ∧ 0 < x.2.2 := by
  have h1 : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), t ≠ 0 := by
    have : ({(0 : ℝ)}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.2 (measure_singleton 0)
    filter_upwards [this] with x hx
    simpa using hx
  have h3 : ∀ᵐ y : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioi 0)), 0 < y := ae_restrict_mem measurableSet_Ioi
  have h23 : ∀ᵐ yz : ℝ × ℝ ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))), 0 < yz.2 :=
    (Measure.quasiMeasurePreserving_snd).ae h3
  exact ((Measure.quasiMeasurePreserving_fst).ae h1).and ((Measure.quasiMeasurePreserving_snd).ae h23)

theorem quasiChar_zero_mul_self (a : ZMod 2) {x : ℝ} (hx : x ≠ 0) :
    ArchR.quasiChar 0 a x * ArchR.quasiChar 0 a x = 1 := by
  rcases lt_or_gt_of_ne hx with h | h
  · have hn : 0 < -x := neg_pos.2 h
    have e : x = -(-x) := (neg_neg x).symm
    rw [e, quasiChar_neg _ _ _ hn.ne', quasiChar_zero_pos _ hn, mul_one, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  · rw [quasiChar_zero_pos _ h, mul_one]

theorem dual_pointwise0 (ν₁ ν₂ : ℂ) (b : ZMod 2)
    (W : ℝ → ℂ) (hWpar : ∀ t : ℝ, W (-t) = (-1 : ℂ) ^ b.val * W t)
    (u₁ u₂ : ℂ) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.principal u₁ b u₂ b)
    (ρ : ℂ)
    (hρ : ∀ τ : ℝ, 0 < τ →
      D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (u₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((τ) / r : ℝ) : ℂ) ^ (u₂) * (Real.exp (-(Real.pi * ((τ) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hDpar : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne τ))
    (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (a₀ sP : ZMod 2) (hsP : sP = b + b)
    (n : ℕ) (hn : n = 0) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (hδpar : ((δ : ℕ) : ZMod 2) = a₀ + b) (s : ℂ)
    (t q p : ℝ) (ht : 0 < t) (hq : 0 < q) (hp0 : 0 < p)
    (hWt : W t + (-1 : ℂ) ^ b.val * W (-t) = (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (b + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (b + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ))) :
    (ArchR.quasiChar 0 sP (-t) * ArchR.quasiChar 0 a₀ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 (n : ZMod 2) q * ArchR.quasiChar 0 a₀ q) *
          (W (-t) * ((((p : ℝ) : ℂ) * ArchR.quasiChar 0 1 t) * ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 t * (((p * q)⁻¹ : ℝ) : ℂ)) ^ δ) * D.W (ArchR.diagOne (a * |t| * p / q))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ)) +
    (ArchR.quasiChar 0 sP (-(-t : ℝ)) * ArchR.quasiChar 0 a₀ (-(-t : ℝ)) * ArchR.quasiChar 0 1 (-t : ℝ) * ArchR.quasiChar 0 (n : ZMod 2) q * ArchR.quasiChar 0 a₀ q) *
          (W (-(-t : ℝ)) * ((((p : ℝ) : ℂ) * ArchR.quasiChar 0 1 (-t : ℝ)) * ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 (-t : ℝ) * (((p * q)⁻¹ : ℝ) : ℂ)) ^ δ) * D.W (ArchR.diagOne (a * |(-t : ℝ)| * p / q))) *
          ((((|(-t : ℝ)| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * (-t : ℝ) ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ)) +
    (ArchR.quasiChar 0 sP (-t) * ArchR.quasiChar 0 a₀ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 (n : ZMod 2) (-q : ℝ) * ArchR.quasiChar 0 a₀ (-q : ℝ)) *
          (W (-t) * ((((p : ℝ) : ℂ) * ArchR.quasiChar 0 1 t) * ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 t * (((p * (-q : ℝ))⁻¹ : ℝ) : ℂ)) ^ δ) * D.W (ArchR.diagOne (a * |t| * p / (-q : ℝ)))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|(-q : ℝ)| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / (-q : ℝ) ^ 2)) : ℂ)) +
    (ArchR.quasiChar 0 sP (-(-t : ℝ)) * ArchR.quasiChar 0 a₀ (-(-t : ℝ)) * ArchR.quasiChar 0 1 (-t : ℝ) * ArchR.quasiChar 0 (n : ZMod 2) (-q : ℝ) * ArchR.quasiChar 0 a₀ (-q : ℝ)) *
          (W (-(-t : ℝ)) * ((((p : ℝ) : ℂ) * ArchR.quasiChar 0 1 (-t : ℝ)) * ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 (-t : ℝ) * (((p * (-q : ℝ))⁻¹ : ℝ) : ℂ)) ^ δ) * D.W (ArchR.diagOne (a * |(-t : ℝ)| * p / (-q : ℝ)))) *
          ((((|(-t : ℝ)| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|(-q : ℝ)| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * (-t : ℝ) ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / (-q : ℝ) ^ 2)) : ℂ)) =
    (2 * (-1 : ℂ) ^ (b.val + δ) * ρ) *
      (((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (b + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t / r : ℝ) : ℂ) ^ (ν₂ + signShift (b + b)) * (Real.exp (-(Real.pi * (t / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (s - 1 / 2 - cP - (u₁ + u₂)) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (u₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ (u₂) * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((p : ℝ) : ℂ) ^ (u₀ - (u₁ + u₂) - 1 - (δ : ℂ)) * ((q : ℝ) : ℂ) ^ (u₀ + cP + (u₁ + u₂) - 2 * s - 2 - (δ : ℂ)) *
          (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / q ^ 2)) : ℂ)) := by
  subst ha1 hn
  have hs0 : sP = 0 := by rw [hsP]; exact (by decide : ∀ b : ZMod 2, b + b = 0) b
  subst hs0
  have ha₀ : a₀ = ((δ : ℕ) : ZMod 2) + b := by
    rw [hδpar, add_assoc, (by decide : ∀ b : ZMod 2, b + b = 0) b, add_zero]
  have hsq : (-1 : ℂ) ^ b.val * (-1 : ℂ) ^ b.val = 1 := by
    rw [← pow_two, ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hW2 : W t = (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (b + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (b + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) / 2 := by
    rw [hWpar t, ← mul_assoc, hsq, one_mul] at hWt
    linear_combination hWt / 2
  clear hWt
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) b with rfl | rfl <;> rcases hδ with rfl | rfl
  ·
    have ha₀' : a₀ = 0 := by
      rw [ha₀]; decide
    subst ha₀' hP₂
    have hce : (RealArchParam.principal u₁ 0 u₂ 0).centralExponent = u₁ + u₂ := rfl
    rw [hce]
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have hz2 : ((0 : ℕ) : ZMod 2) = 0 := Nat.cast_zero
    have hm11 : (-1 : ℂ) ^ (1 + 1) = 1 := by norm_num
    simp only [v0, v1, hm11, pow_zero, pow_one, neg_neg, hz2, one_mul, mul_one, zero_add, add_zero, h11]
      at hDpar hWpar hW2 ⊢
    have eτ : 0 < t * p / q := by positivity
    have r8 : |t| = t := abs_of_pos ht
    have r9 : |(-t)| = t := by rw [abs_neg, r8]
    rw [r9, r8]
    rw [show (-1 : ℝ) * t * p / q = -(t * p / q) by ring,
      show (-1 : ℝ) * t * p / -q = t * p / q by ring]
    rw [hDpar _ eτ, hρ _ eτ, hWpar t, hW2]
    simp only [quasiChar_neg _ _ _ ht.ne', quasiChar_neg _ _ _ hq.ne', quasiChar_zero_pos _ ht, quasiChar_zero_pos _ hq,
      v0, v1, pow_zero, pow_one, one_mul, mul_one, neg_neg]
    have r5 : |q| = q := abs_of_pos hq
    have r7 : |(-q)| = q := by rw [abs_neg, r5]
    rw [r7, r5, neg_sq t, neg_sq q]
    have he1 : ((Real.exp (-(Real.pi * (-1) ^ 2 / p ^ 2)) : ℝ) : ℂ) = ((Real.exp (-(Real.pi / p ^ 2)) : ℝ) : ℂ) := by
      congr 1; congr 1; ring
    have he2 : ((Real.exp (-(Real.pi * (-1) ^ 2 / q ^ 2)) : ℝ) : ℂ) = ((Real.exp (-(Real.pi / q ^ 2)) : ℝ) : ℂ) := by
      congr 1; congr 1; ring
    have hi1 : (((p * -q)⁻¹ : ℝ) : ℂ) = -(((p : ℝ) : ℂ) * ((q : ℝ) : ℂ))⁻¹ := by push_cast; rw [mul_neg, inv_neg]
    have hi2 : (((p * q)⁻¹ : ℝ) : ℂ) = (((p : ℝ) : ℂ) * ((q : ℝ) : ℂ))⁻¹ := by push_cast; ring
    rw [he1, he2]
    try rw [hi1]
    try rw [hi2]
    set Gpt : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift 0) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift 0) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGpt
    set Gqτ : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (u₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ (u₂) * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGqτ
    set tA : ℂ := ((t : ℝ) : ℂ) ^ (s - 5 / 2 - cP - (u₁ + u₂)) with htA
    set qC : ℂ := ((q : ℝ) : ℂ) ^ (u₀ + cP + (u₁ + u₂) - 2 * s - 1) with hqC
    set pE : ℂ := ((p : ℝ) : ℂ) ^ (u₀ - (u₁ + u₂) - 3) with hpE
    set tα : ℂ := ((t : ℝ) : ℂ) ^ (s - 1 / 2 - cP - (u₁ + u₂)) with htα
    set pβ : ℂ := ((p : ℝ) : ℂ) ^ (u₀ - (u₁ + u₂) - 1 - ((0 : ℕ) : ℂ)) with hpβ
    set qγ : ℂ := ((q : ℝ) : ℂ) ^ (u₀ + cP + (u₁ + u₂) - 2 * s - 2 - ((0 : ℕ) : ℂ)) with hqγ
    set E1 : ℂ := ((Real.exp (-(Real.pi / p ^ 2)) : ℝ) : ℂ) with hE1
    set Et : ℂ := ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℝ) : ℂ) with hEt
    set E2 : ℂ := ((Real.exp (-(Real.pi / q ^ 2)) : ℝ) : ℂ) with hE2
    set Wv : ℂ := D.W (ArchR.diagOne (t * p / q)) with hWv
    set τc : ℂ := ((t * p / q : ℝ) : ℂ) with hτc
    have hτc' : τc = (t : ℂ) * (p : ℂ) / (q : ℂ) := by rw [hτc]; push_cast; ring
    have hp : tA * ((t : ℝ) : ℂ) * ((t : ℝ) : ℂ) * (pE * ((p : ℝ) : ℂ) * ((p : ℝ) : ℂ)) * (qC * ((q : ℝ) : ℂ)⁻¹) = tα * pβ * qγ := by
      rw [htA, hpE, hqC, htα, hpβ, hqγ, ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp hp0, ofReal_cpow_eq_exp hq,
        ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp hp0, ofReal_cpow_eq_exp hq,
        ofReal_eq_exp_log ht, ofReal_eq_exp_log hp0, ofReal_eq_exp_log hq]
      repeat rw [← Complex.exp_neg]
      simp only [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have ht0 : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
    have hq0 : ((q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hq.ne'
    have hp0' : ((p : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hp0.ne'
    rw [hτc']
    clear_value Gpt Gqτ tA qC pE tα pβ qγ E1 Et E2 τc
    push_cast
    linear_combination (2 * (1 : ℂ) * ρ * Gpt * Gqτ * E1 * Et * E2) * hp
  ·
    have ha₀' : a₀ = 1 := by
      rw [ha₀]; decide
    subst ha₀' hP₂
    have hce : (RealArchParam.principal u₁ 0 u₂ 0).centralExponent = u₁ + u₂ := rfl
    rw [hce]
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have hz2 : ((0 : ℕ) : ZMod 2) = 0 := Nat.cast_zero
    have hm11 : (-1 : ℂ) ^ (1 + 1) = 1 := by norm_num
    simp only [v0, v1, hm11, pow_zero, pow_one, neg_neg, hz2, one_mul, mul_one, zero_add, add_zero, h11]
      at hDpar hWpar hW2 ⊢
    have eτ : 0 < t * p / q := by positivity
    have r8 : |t| = t := abs_of_pos ht
    have r9 : |(-t)| = t := by rw [abs_neg, r8]
    rw [r9, r8]
    rw [show (-1 : ℝ) * t * p / q = -(t * p / q) by ring,
      show (-1 : ℝ) * t * p / -q = t * p / q by ring]
    rw [hDpar _ eτ, hρ _ eτ, hWpar t, hW2]
    simp only [quasiChar_neg _ _ _ ht.ne', quasiChar_neg _ _ _ hq.ne', quasiChar_zero_pos _ ht, quasiChar_zero_pos _ hq,
      v0, v1, pow_zero, pow_one, one_mul, mul_one, neg_neg]
    have r5 : |q| = q := abs_of_pos hq
    have r7 : |(-q)| = q := by rw [abs_neg, r5]
    rw [r7, r5, neg_sq t, neg_sq q]
    have he1 : ((Real.exp (-(Real.pi * (-1) ^ 2 / p ^ 2)) : ℝ) : ℂ) = ((Real.exp (-(Real.pi / p ^ 2)) : ℝ) : ℂ) := by
      congr 1; congr 1; ring
    have he2 : ((Real.exp (-(Real.pi * (-1) ^ 2 / q ^ 2)) : ℝ) : ℂ) = ((Real.exp (-(Real.pi / q ^ 2)) : ℝ) : ℂ) := by
      congr 1; congr 1; ring
    have hi1 : (((p * -q)⁻¹ : ℝ) : ℂ) = -(((p : ℝ) : ℂ) * ((q : ℝ) : ℂ))⁻¹ := by push_cast; rw [mul_neg, inv_neg]
    have hi2 : (((p * q)⁻¹ : ℝ) : ℂ) = (((p : ℝ) : ℂ) * ((q : ℝ) : ℂ))⁻¹ := by push_cast; ring
    rw [he1, he2]
    try rw [hi1]
    try rw [hi2]
    set Gpt : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift 0) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift 0) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGpt
    set Gqτ : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (u₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ (u₂) * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGqτ
    set tA : ℂ := ((t : ℝ) : ℂ) ^ (s - 5 / 2 - cP - (u₁ + u₂)) with htA
    set qC : ℂ := ((q : ℝ) : ℂ) ^ (u₀ + cP + (u₁ + u₂) - 2 * s - 1) with hqC
    set pE : ℂ := ((p : ℝ) : ℂ) ^ (u₀ - (u₁ + u₂) - 3) with hpE
    set tα : ℂ := ((t : ℝ) : ℂ) ^ (s - 1 / 2 - cP - (u₁ + u₂)) with htα
    set pβ : ℂ := ((p : ℝ) : ℂ) ^ (u₀ - (u₁ + u₂) - 1 - ((1 : ℕ) : ℂ)) with hpβ
    set qγ : ℂ := ((q : ℝ) : ℂ) ^ (u₀ + cP + (u₁ + u₂) - 2 * s - 2 - ((1 : ℕ) : ℂ)) with hqγ
    set E1 : ℂ := ((Real.exp (-(Real.pi / p ^ 2)) : ℝ) : ℂ) with hE1
    set Et : ℂ := ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℝ) : ℂ) with hEt
    set E2 : ℂ := ((Real.exp (-(Real.pi / q ^ 2)) : ℝ) : ℂ) with hE2
    set Wv : ℂ := D.W (ArchR.diagOne (t * p / q)) with hWv
    set τc : ℂ := ((t * p / q : ℝ) : ℂ) with hτc
    have hτc' : τc = (t : ℂ) * (p : ℂ) / (q : ℂ) := by rw [hτc]; push_cast; ring
    have hp : tA * ((t : ℝ) : ℂ) * ((t : ℝ) : ℂ) * (pE * ((p : ℝ) : ℂ) * ((p : ℝ) : ℂ) * ((p : ℝ) : ℂ)⁻¹) * (qC * ((q : ℝ) : ℂ)⁻¹ * ((q : ℝ) : ℂ)⁻¹) = tα * pβ * qγ := by
      rw [htA, hpE, hqC, htα, hpβ, hqγ, ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp hp0, ofReal_cpow_eq_exp hq,
        ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp hp0, ofReal_cpow_eq_exp hq,
        ofReal_eq_exp_log ht, ofReal_eq_exp_log hp0, ofReal_eq_exp_log hq]
      repeat rw [← Complex.exp_neg]
      simp only [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have ht0 : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
    have hq0 : ((q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hq.ne'
    have hp0' : ((p : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hp0.ne'
    rw [hτc']
    clear_value Gpt Gqτ tA qC pE tα pβ qγ E1 Et E2 τc
    push_cast
    linear_combination (2 * (-1 : ℂ) * ρ * Gpt * Gqτ * E1 * Et * E2) * hp
  ·
    have ha₀' : a₀ = 1 := by
      rw [ha₀]; decide
    subst ha₀' hP₂
    have hce : (RealArchParam.principal u₁ 1 u₂ 1).centralExponent = u₁ + u₂ := rfl
    rw [hce]
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have hz2 : ((0 : ℕ) : ZMod 2) = 0 := Nat.cast_zero
    have hm11 : (-1 : ℂ) ^ (1 + 1) = 1 := by norm_num
    simp only [v0, v1, hm11, pow_zero, pow_one, neg_neg, hz2, one_mul, mul_one, zero_add, add_zero, h11]
      at hDpar hWpar hW2 ⊢
    have eτ : 0 < t * p / q := by positivity
    have r8 : |t| = t := abs_of_pos ht
    have r9 : |(-t)| = t := by rw [abs_neg, r8]
    rw [r9, r8]
    rw [show (-1 : ℝ) * t * p / q = -(t * p / q) by ring,
      show (-1 : ℝ) * t * p / -q = t * p / q by ring]
    rw [hDpar _ eτ, hρ _ eτ, hWpar t, hW2]
    simp only [quasiChar_neg _ _ _ ht.ne', quasiChar_neg _ _ _ hq.ne', quasiChar_zero_pos _ ht, quasiChar_zero_pos _ hq,
      v0, v1, pow_zero, pow_one, one_mul, mul_one, neg_neg]
    have r5 : |q| = q := abs_of_pos hq
    have r7 : |(-q)| = q := by rw [abs_neg, r5]
    rw [r7, r5, neg_sq t, neg_sq q]
    have he1 : ((Real.exp (-(Real.pi * (-1) ^ 2 / p ^ 2)) : ℝ) : ℂ) = ((Real.exp (-(Real.pi / p ^ 2)) : ℝ) : ℂ) := by
      congr 1; congr 1; ring
    have he2 : ((Real.exp (-(Real.pi * (-1) ^ 2 / q ^ 2)) : ℝ) : ℂ) = ((Real.exp (-(Real.pi / q ^ 2)) : ℝ) : ℂ) := by
      congr 1; congr 1; ring
    have hi1 : (((p * -q)⁻¹ : ℝ) : ℂ) = -(((p : ℝ) : ℂ) * ((q : ℝ) : ℂ))⁻¹ := by push_cast; rw [mul_neg, inv_neg]
    have hi2 : (((p * q)⁻¹ : ℝ) : ℂ) = (((p : ℝ) : ℂ) * ((q : ℝ) : ℂ))⁻¹ := by push_cast; ring
    rw [he1, he2]
    try rw [hi1]
    try rw [hi2]
    set Gpt : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift 0) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift 0) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGpt
    set Gqτ : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (u₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ (u₂) * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGqτ
    set tA : ℂ := ((t : ℝ) : ℂ) ^ (s - 5 / 2 - cP - (u₁ + u₂)) with htA
    set qC : ℂ := ((q : ℝ) : ℂ) ^ (u₀ + cP + (u₁ + u₂) - 2 * s - 1) with hqC
    set pE : ℂ := ((p : ℝ) : ℂ) ^ (u₀ - (u₁ + u₂) - 3) with hpE
    set tα : ℂ := ((t : ℝ) : ℂ) ^ (s - 1 / 2 - cP - (u₁ + u₂)) with htα
    set pβ : ℂ := ((p : ℝ) : ℂ) ^ (u₀ - (u₁ + u₂) - 1 - ((0 : ℕ) : ℂ)) with hpβ
    set qγ : ℂ := ((q : ℝ) : ℂ) ^ (u₀ + cP + (u₁ + u₂) - 2 * s - 2 - ((0 : ℕ) : ℂ)) with hqγ
    set E1 : ℂ := ((Real.exp (-(Real.pi / p ^ 2)) : ℝ) : ℂ) with hE1
    set Et : ℂ := ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℝ) : ℂ) with hEt
    set E2 : ℂ := ((Real.exp (-(Real.pi / q ^ 2)) : ℝ) : ℂ) with hE2
    set Wv : ℂ := D.W (ArchR.diagOne (t * p / q)) with hWv
    set τc : ℂ := ((t * p / q : ℝ) : ℂ) with hτc
    have hτc' : τc = (t : ℂ) * (p : ℂ) / (q : ℂ) := by rw [hτc]; push_cast; ring
    have hp : tA * ((t : ℝ) : ℂ) * ((t : ℝ) : ℂ) * (pE * ((p : ℝ) : ℂ) * ((p : ℝ) : ℂ)) * (qC * ((q : ℝ) : ℂ)⁻¹) = tα * pβ * qγ := by
      rw [htA, hpE, hqC, htα, hpβ, hqγ, ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp hp0, ofReal_cpow_eq_exp hq,
        ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp hp0, ofReal_cpow_eq_exp hq,
        ofReal_eq_exp_log ht, ofReal_eq_exp_log hp0, ofReal_eq_exp_log hq]
      repeat rw [← Complex.exp_neg]
      simp only [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have ht0 : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
    have hq0 : ((q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hq.ne'
    have hp0' : ((p : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hp0.ne'
    rw [hτc']
    clear_value Gpt Gqτ tA qC pE tα pβ qγ E1 Et E2 τc
    push_cast
    linear_combination (2 * (-1 : ℂ) * ρ * Gpt * Gqτ * E1 * Et * E2) * hp
  ·
    have ha₀' : a₀ = 0 := by
      rw [ha₀]; decide
    subst ha₀' hP₂
    have hce : (RealArchParam.principal u₁ 1 u₂ 1).centralExponent = u₁ + u₂ := rfl
    rw [hce]
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have hz2 : ((0 : ℕ) : ZMod 2) = 0 := Nat.cast_zero
    have hm11 : (-1 : ℂ) ^ (1 + 1) = 1 := by norm_num
    simp only [v0, v1, hm11, pow_zero, pow_one, neg_neg, hz2, one_mul, mul_one, zero_add, add_zero, h11]
      at hDpar hWpar hW2 ⊢
    have eτ : 0 < t * p / q := by positivity
    have r8 : |t| = t := abs_of_pos ht
    have r9 : |(-t)| = t := by rw [abs_neg, r8]
    rw [r9, r8]
    rw [show (-1 : ℝ) * t * p / q = -(t * p / q) by ring,
      show (-1 : ℝ) * t * p / -q = t * p / q by ring]
    rw [hDpar _ eτ, hρ _ eτ, hWpar t, hW2]
    simp only [quasiChar_neg _ _ _ ht.ne', quasiChar_neg _ _ _ hq.ne', quasiChar_zero_pos _ ht, quasiChar_zero_pos _ hq,
      v0, v1, pow_zero, pow_one, one_mul, mul_one, neg_neg]
    have r5 : |q| = q := abs_of_pos hq
    have r7 : |(-q)| = q := by rw [abs_neg, r5]
    rw [r7, r5, neg_sq t, neg_sq q]
    have he1 : ((Real.exp (-(Real.pi * (-1) ^ 2 / p ^ 2)) : ℝ) : ℂ) = ((Real.exp (-(Real.pi / p ^ 2)) : ℝ) : ℂ) := by
      congr 1; congr 1; ring
    have he2 : ((Real.exp (-(Real.pi * (-1) ^ 2 / q ^ 2)) : ℝ) : ℂ) = ((Real.exp (-(Real.pi / q ^ 2)) : ℝ) : ℂ) := by
      congr 1; congr 1; ring
    have hi1 : (((p * -q)⁻¹ : ℝ) : ℂ) = -(((p : ℝ) : ℂ) * ((q : ℝ) : ℂ))⁻¹ := by push_cast; rw [mul_neg, inv_neg]
    have hi2 : (((p * q)⁻¹ : ℝ) : ℂ) = (((p : ℝ) : ℂ) * ((q : ℝ) : ℂ))⁻¹ := by push_cast; ring
    rw [he1, he2]
    try rw [hi1]
    try rw [hi2]
    set Gpt : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift 0) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift 0) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGpt
    set Gqτ : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (u₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ (u₂) * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGqτ
    set tA : ℂ := ((t : ℝ) : ℂ) ^ (s - 5 / 2 - cP - (u₁ + u₂)) with htA
    set qC : ℂ := ((q : ℝ) : ℂ) ^ (u₀ + cP + (u₁ + u₂) - 2 * s - 1) with hqC
    set pE : ℂ := ((p : ℝ) : ℂ) ^ (u₀ - (u₁ + u₂) - 3) with hpE
    set tα : ℂ := ((t : ℝ) : ℂ) ^ (s - 1 / 2 - cP - (u₁ + u₂)) with htα
    set pβ : ℂ := ((p : ℝ) : ℂ) ^ (u₀ - (u₁ + u₂) - 1 - ((1 : ℕ) : ℂ)) with hpβ
    set qγ : ℂ := ((q : ℝ) : ℂ) ^ (u₀ + cP + (u₁ + u₂) - 2 * s - 2 - ((1 : ℕ) : ℂ)) with hqγ
    set E1 : ℂ := ((Real.exp (-(Real.pi / p ^ 2)) : ℝ) : ℂ) with hE1
    set Et : ℂ := ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℝ) : ℂ) with hEt
    set E2 : ℂ := ((Real.exp (-(Real.pi / q ^ 2)) : ℝ) : ℂ) with hE2
    set Wv : ℂ := D.W (ArchR.diagOne (t * p / q)) with hWv
    set τc : ℂ := ((t * p / q : ℝ) : ℂ) with hτc
    have hτc' : τc = (t : ℂ) * (p : ℂ) / (q : ℂ) := by rw [hτc]; push_cast; ring
    have hp : tA * ((t : ℝ) : ℂ) * ((t : ℝ) : ℂ) * (pE * ((p : ℝ) : ℂ) * ((p : ℝ) : ℂ) * ((p : ℝ) : ℂ)⁻¹) * (qC * ((q : ℝ) : ℂ)⁻¹ * ((q : ℝ) : ℂ)⁻¹) = tα * pβ * qγ := by
      rw [htA, hpE, hqC, htα, hpβ, hqγ, ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp hp0, ofReal_cpow_eq_exp hq,
        ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp hp0, ofReal_cpow_eq_exp hq,
        ofReal_eq_exp_log ht, ofReal_eq_exp_log hp0, ofReal_eq_exp_log hq]
      repeat rw [← Complex.exp_neg]
      simp only [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have ht0 : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
    have hq0 : ((q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hq.ne'
    have hp0' : ((p : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hp0.ne'
    rw [hτc']
    clear_value Gpt Gqτ tA qC pE tα pβ qγ E1 Et E2 τc
    push_cast
    linear_combination (2 * (1 : ℂ) * ρ * Gpt * Gqτ * E1 * Et * E2) * hp

end Eval00

open Eval00 in
theorem solution
    (ν₁ ν₂ : ℂ) (b : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hWpar : ∀ t : ℝ, W (-t) = (-1 : ℂ) ^ b.val * W t)
    (hW : ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (b + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (b + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (u₁ u₂ : ℂ) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.principal u₁ b u₂ b)
    (ρ : ℂ)
    (hρ : ∀ τ : ℝ, 0 < τ →
      D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (u₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((τ) / r : ℝ) : ℂ) ^ (u₂) * (Real.exp (-(Real.pi * ((τ) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hDpar : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne τ))
    (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (hcP : cP = ν₁ + ν₂) (a₀ sP : ZMod 2) (hsP : sP = b + b)
    (n : ℕ) (hn : n = 0) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (hδpar : ((δ : ℕ) : ZMod 2) = a₀ + b) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Complex.Gammaℝ (2 * s - cP - P₂.centralExponent + n + 1) *
        (∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ),
          (ArchR.quasiChar 0 sP (-t) * ArchR.quasiChar 0 a₀ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 (n : ZMod 2) q * ArchR.quasiChar 0 a₀ q) *
          (W (-t) * ((((p : ℝ) : ℂ) * ArchR.quasiChar 0 1 t) * ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 t * (((p * q)⁻¹ : ℝ) : ℂ)) ^ δ) * D.W (ArchR.diagOne (a * |t| * p / q))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ))) =
      (-1 : ℂ) ^ (b.val + δ) * ρ *
        ((Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₀) + signShift (b + a₀))) *
          Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₀) + signShift (b + a₀)))) *
          ((Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₁) + signShift (b + b))) *
            Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₁) + signShift (b + b)))) *
            (Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₂) + signShift (b + b))) *
              Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₂) + signShift (b + b)))))) := by
  have ha : a ≠ 0 := by rw [ha1]; norm_num
  obtain ⟨σI, hI⟩ :=
    LanglandsTunnell.Converse.exists_forall_integrable_dualQuadruple_and_torusTriple_detPow_colHarmonic_of_evenSheet
      ν₁ ν₂ b W hWc hWpar hW D a ha u₀ cP a₀ sP n δ hδ
  have hce : P₂.centralExponent = u₁ + u₂ := by rw [hP₂]; rfl
  have hsre : ∀ z : ZMod 2, (signShift z).re = 0 ∨ (signShift z).re = 1 := by
    intro z; unfold signShift; split_ifs <;> simp
  set R : ℝ := |u₀.re| + |ν₁.re| + |ν₂.re| + |u₁.re| + |u₂.re| + |cP.re| + 4 with hR
  refine ⟨max σI R, fun s hs => ?_⟩
  have hsI : σI < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hsR : R < s.re := lt_of_le_of_lt (le_max_right _ _) hs

  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ → ℝ → ℂ, ∀ t q p : ℝ, F t q p =
          (ArchR.quasiChar 0 sP (-t) * ArchR.quasiChar 0 a₀ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 (n : ZMod 2) q * ArchR.quasiChar 0 a₀ q) *
          (W (-t) * ((((p : ℝ) : ℂ) * ArchR.quasiChar 0 1 t) * ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 t * (((p * q)⁻¹ : ℝ) : ℂ)) ^ δ) * D.W (ArchR.diagOne (a * |t| * p / q))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ)) := ⟨_, fun _ _ _ => rfl⟩
  simp only [← hF]
  set ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi 0) with hν

  have hFint : Integrable (fun x : ℝ × ℝ × ℝ => F x.1 x.2.1 x.2.2) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ν)) := by
    rcases hδ with hδ0 | hδ1
    · have h := (hI s hsI).2 1 0
      refine h.congr (ae_of_all _ fun x => ?_)
      simp only [hF, hδ0, pow_zero, mul_one, one_mul, zero_mul, add_zero]
    · have h := (hI s hsI).2 0 1
      refine h.congr ?_
      filter_upwards [Eval00.ae_good3] with x hx
      obtain ⟨hx1, hx3⟩ := hx
      have hb : (((x.2.2 : ℝ) : ℂ) * ArchR.quasiChar 0 1 x.1) *
          ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 x.1 * (((x.2.2 * x.2.1)⁻¹ : ℝ) : ℂ)) =
          (a : ℂ) ^ 2 * ((x.2.1⁻¹ : ℝ) : ℂ) := by
        have hχ := Eval00.quasiChar_zero_mul_self 1 hx1
        have hp0 : ((x.2.2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx3.ne'
        calc (((x.2.2 : ℝ) : ℂ) * ArchR.quasiChar 0 1 x.1) *
              ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 x.1 * (((x.2.2 * x.2.1)⁻¹ : ℝ) : ℂ))
            = (a : ℂ) ^ 2 * (ArchR.quasiChar 0 1 x.1 * ArchR.quasiChar 0 1 x.1) *
                (((x.2.2 : ℝ) : ℂ) * (((x.2.2 * x.2.1)⁻¹ : ℝ) : ℂ)) := by ring
          _ = (a : ℂ) ^ 2 * ((x.2.1⁻¹ : ℝ) : ℂ) := by
            rw [hχ, mul_one]
            push_cast
            rw [mul_inv, ← mul_assoc (x.2.2 : ℂ), mul_inv_cancel₀ hp0, one_mul]
      simp only [hF, hδ1, pow_one, one_mul, zero_mul, zero_add, hb]

  have hiter : (∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ), F t q p) =
      ∫ x, F x.1 x.2.1 x.2.2 ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ν)) := by
    rw [integral_prod (f := fun x : ℝ × ℝ × ℝ => F x.1 x.2.1 x.2.2) hFint]
    refine integral_congr_ae ?_
    filter_upwards [hFint.prod_right_ae] with t ht
    exact (integral_prod (f := fun yz : ℝ × ℝ => F t yz.1 yz.2) ht).symm

  have hΦ : MeasurePreserving (⇑(MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod ν) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ν)) :=
    measurePreserving_prodAssoc _ _ _
  have hFa : Integrable ((fun x : ℝ × ℝ × ℝ => F x.1 x.2.1 x.2.2) ∘ ⇑(MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod ν) :=
    (hΦ.integrable_comp hFint.aestronglyMeasurable).2 hFint
  have step0 : ∫ x, F x.1 x.2.1 x.2.2 ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ν)) =
      ∫ pr : (ℝ × ℝ) × ℝ, F pr.1.1 pr.1.2 pr.2 ∂(((volume : Measure ℝ).prod (volume : Measure ℝ)).prod ν) := by
    rw [← hΦ.integral_comp (MeasurableEquiv.prodAssoc).measurableEmbedding]
    rfl
  have step1 : ∫ pr : (ℝ × ℝ) × ℝ, F pr.1.1 pr.1.2 pr.2 ∂(((volume : Measure ℝ).prod (volume : Measure ℝ)).prod ν) =
      ∫ pq : ℝ × ℝ, (∫ p, F pq.1 pq.2 p ∂ν) ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    integral_prod (f := fun pr : (ℝ × ℝ) × ℝ => F pr.1.1 pr.1.2 pr.2) hFa
  have hh : Integrable (fun pq : ℝ × ℝ => ∫ p, F pq.1 pq.2 p ∂ν) ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    hFa.integral_prod_left
  have step2 := LanglandsTunnell.integral_prod_eq_setIntegral_Ioi_setIntegral_Ioi_sum_reflections
    (fun pq : ℝ × ℝ => ∫ p, F pq.1 pq.2 p ∂ν) hh
  have hsl : ∀ᵐ pq : ℝ × ℝ ∂((volume : Measure ℝ).prod (volume : Measure ℝ)), Integrable (fun p => F pq.1 pq.2 p) ν :=
    hFa.prod_right_ae
  have hmp1 : MeasurePreserving (fun pq : ℝ × ℝ => (-pq.1, pq.2)) ((volume : Measure ℝ).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id (volume : Measure ℝ))
  have hmp2 : MeasurePreserving (fun pq : ℝ × ℝ => (pq.1, -pq.2)) ((volume : Measure ℝ).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hsl2 := hmp1.quasiMeasurePreserving.ae hsl
  have hsl3 := hmp2.quasiMeasurePreserving.ae hsl
  have hsl4 := hmp1.quasiMeasurePreserving.ae hsl3
  simp only at hsl2 hsl3 hsl4

  have key : ∀ᵐ pq : ℝ × ℝ ∂((volume : Measure ℝ).prod (volume : Measure ℝ)), 0 < pq.1 → 0 < pq.2 →
      (∫ p, F pq.1 pq.2 p ∂ν) + (∫ p, F (-pq.1) pq.2 p ∂ν) + (∫ p, F pq.1 (-pq.2) p ∂ν) + (∫ p, F (-pq.1) (-pq.2) p ∂ν) =
      (2 * (-1 : ℂ) ^ (b.val + δ) * ρ) * ∫ p in Set.Ioi (0 : ℝ), (((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (b + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((pq.1 / r : ℝ) : ℂ) ^ (ν₂ + signShift (b + b)) * (Real.exp (-(Real.pi * (pq.1 / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((pq.1 : ℝ) : ℂ) ^ (s - 1 / 2 - cP - (u₁ + u₂)) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ u₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((pq.1 * p / pq.2) / r : ℝ) : ℂ) ^ u₂ * (Real.exp (-(Real.pi * ((pq.1 * p / pq.2) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((p : ℝ) : ℂ) ^ (u₀ - (u₁ + u₂) - 1 - (δ : ℂ)) * ((pq.2 : ℝ) : ℂ) ^ (u₀ + cP + (u₁ + u₂) - 2 * s - 2 - (δ : ℂ)) *
          (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * pq.1 ^ 2 * p ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / pq.2 ^ 2)) : ℂ)) := by
    filter_upwards [hsl, hsl2, hsl3, hsl4] with pq i1 i2 i3 i4 ht hq
    have i12 : Integrable (fun p => F pq.1 pq.2 p + F (-pq.1) pq.2 p) ν := i1.add i2
    have i123 : Integrable (fun p => F pq.1 pq.2 p + F (-pq.1) pq.2 p + F pq.1 (-pq.2) p) ν := i12.add i3
    rw [← integral_add i1 i2, ← integral_add i12 i3, ← integral_add i123 i4, hν, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun p hp => ?_
    have hp : 0 < p := hp
    rw [hF, hF, hF, hF]
    exact Eval00.dual_pointwise0 ν₁ ν₂ b W hWpar u₁ u₂ D hP₂ ρ hρ hDpar a ha1 u₀ cP a₀ sP hsP n hn δ hδ hδpar s
      pq.1 pq.2 p ht hq hp (hW pq.1 ht)
  have key' := Measure.ae_ae_of_ae_prod key
  dsimp only at key' step2
  rw [hiter, step0, step1, step2]
  have step3 : ∫ t in Set.Ioi (0 : ℝ), ∫ q in Set.Ioi (0 : ℝ),
      ((∫ p, F t q p ∂ν) + (∫ p, F (-t) q p ∂ν) + (∫ p, F t (-q) p ∂ν) + (∫ p, F (-t) (-q) p ∂ν)) =
      ∫ t in Set.Ioi (0 : ℝ), ∫ q in Set.Ioi (0 : ℝ),
        (2 * (-1 : ℂ) ^ (b.val + δ) * ρ) * ∫ p in Set.Ioi (0 : ℝ), (((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (b + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t / r : ℝ) : ℂ) ^ (ν₂ + signShift (b + b)) * (Real.exp (-(Real.pi * (t / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (s - 1 / 2 - cP - (u₁ + u₂)) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ u₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ u₂ * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((p : ℝ) : ℂ) ^ (u₀ - (u₁ + u₂) - 1 - (δ : ℂ)) * ((q : ℝ) : ℂ) ^ (u₀ + cP + (u₁ + u₂) - 2 * s - 2 - (δ : ℂ)) *
          (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / q ^ 2)) : ℂ)) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae key'] with t ht hk
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hk] with q hq hk2
    exact hk2 ht hq
  rw [step3]
  simp only [integral_const_mul]

  rcases eq_or_ne ρ 0 with hρ0 | hρ0
  · simp [hρ0]
  have hCst : (2 * (-1 : ℂ) ^ (b.val + δ) * ρ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (by norm_num))) hρ0
  have hswap : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), 0 < t →
      (∫ q in Set.Ioi (0 : ℝ), ∫ p in Set.Ioi (0 : ℝ), (((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (b + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t / r : ℝ) : ℂ) ^ (ν₂ + signShift (b + b)) * (Real.exp (-(Real.pi * (t / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (s - 1 / 2 - cP - (u₁ + u₂)) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ u₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ u₂ * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((p : ℝ) : ℂ) ^ (u₀ - (u₁ + u₂) - 1 - (δ : ℂ)) * ((q : ℝ) : ℂ) ^ (u₀ + cP + (u₁ + u₂) - 2 * s - 2 - (δ : ℂ)) *
          (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / q ^ 2)) : ℂ))) =
      ∫ p in Set.Ioi (0 : ℝ), ∫ q in Set.Ioi (0 : ℝ), (((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (b + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t / r : ℝ) : ℂ) ^ (ν₂ + signShift (b + b)) * (Real.exp (-(Real.pi * (t / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (s - 1 / 2 - cP - (u₁ + u₂)) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ u₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ u₂ * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((p : ℝ) : ℂ) ^ (u₀ - (u₁ + u₂) - 1 - (δ : ℂ)) * ((q : ℝ) : ℂ) ^ (u₀ + cP + (u₁ + u₂) - 2 * s - 2 - (δ : ℂ)) *
          (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / q ^ 2)) : ℂ)) := by
    have hst : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), Integrable (fun qp : ℝ × ℝ => F t qp.1 qp.2) ((volume : Measure ℝ).prod ν) :=
      hFint.prod_right_ae
    have hst' : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), Integrable (fun qp : ℝ × ℝ => F (-t) qp.1 qp.2) ((volume : Measure ℝ).prod ν) :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hst
    have hmq : MeasurePreserving (fun qp : ℝ × ℝ => (-qp.1, qp.2)) ((volume : Measure ℝ).prod ν) ((volume : Measure ℝ).prod ν) :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id ν)
    filter_upwards [hst, hst'] with t i1 i2 ht
    have i3 : Integrable (fun qp : ℝ × ℝ => F t (-qp.1) qp.2) ((volume : Measure ℝ).prod ν) :=
      (hmq.integrable_comp i1.aestronglyMeasurable).mpr i1
    have i4 : Integrable (fun qp : ℝ × ℝ => F (-t) (-qp.1) qp.2) ((volume : Measure ℝ).prod ν) :=
      (hmq.integrable_comp i2.aestronglyMeasurable).mpr i2
    have hsum0 : Integrable (fun qp : ℝ × ℝ => (2 * (-1 : ℂ) ^ (b.val + δ) * ρ)⁻¹ *
        (F t qp.1 qp.2 + F (-t) qp.1 qp.2 + F t (-qp.1) qp.2 + F (-t) (-qp.1) qp.2))
        ((volume : Measure ℝ).prod ν) := (((i1.add i2).add i3).add i4).const_mul _
    have hmeas_eq : ((volume : Measure ℝ).prod ν) = ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (Set.univ ×ˢ Set.Ioi 0) := by
      rw [hν, ← Measure.prod_restrict, Measure.restrict_univ]
    have hsum : Integrable (fun qp : ℝ × ℝ => (2 * (-1 : ℂ) ^ (b.val + δ) * ρ)⁻¹ *
        (F t qp.1 qp.2 + F (-t) qp.1 qp.2 + F t (-qp.1) qp.2 + F (-t) (-qp.1) qp.2))
        (((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (Set.Ioi 0 ×ˢ Set.Ioi 0)) := by
      rw [hmeas_eq] at hsum0
      exact hsum0.mono_measure (Measure.restrict_mono (Set.prod_mono (Set.subset_univ _) subset_rfl) le_rfl)
    have hK : Integrable (Function.uncurry fun (q p : ℝ) => ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (b + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t / r : ℝ) : ℂ) ^ (ν₂ + signShift (b + b)) * (Real.exp (-(Real.pi * (t / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (s - 1 / 2 - cP - (u₁ + u₂)) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ u₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ u₂ * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((p : ℝ) : ℂ) ^ (u₀ - (u₁ + u₂) - 1 - (δ : ℂ)) * ((q : ℝ) : ℂ) ^ (u₀ + cP + (u₁ + u₂) - 2 * s - 2 - (δ : ℂ)) *
          (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / q ^ 2)) : ℂ))
        (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))) := by
      rw [Measure.prod_restrict]
      refine hsum.congr ?_
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with qp hqp
      obtain ⟨hq, hp⟩ := hqp
      have hq : 0 < qp.1 := hq
      have hp : 0 < qp.2 := hp
      have e := Eval00.dual_pointwise0 ν₁ ν₂ b W hWpar u₁ u₂ D hP₂ ρ hρ hDpar a ha1 u₀ cP a₀ sP hsP n hn δ hδ hδpar s
        t qp.1 qp.2 ht hq hp (hW t ht)
      rw [← hF, ← hF, ← hF, ← hF] at e
      dsimp only [Function.uncurry]
      rw [e, ← mul_assoc, inv_mul_cancel₀ hCst, one_mul]
    exact integral_integral_swap hK
  have step4 : ∫ t in Set.Ioi (0 : ℝ), ∫ q in Set.Ioi (0 : ℝ), ∫ p in Set.Ioi (0 : ℝ), (((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (b + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t / r : ℝ) : ℂ) ^ (ν₂ + signShift (b + b)) * (Real.exp (-(Real.pi * (t / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (s - 1 / 2 - cP - (u₁ + u₂)) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ u₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ u₂ * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((p : ℝ) : ℂ) ^ (u₀ - (u₁ + u₂) - 1 - (δ : ℂ)) * ((q : ℝ) : ℂ) ^ (u₀ + cP + (u₁ + u₂) - 2 * s - 2 - (δ : ℂ)) *
          (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / q ^ 2)) : ℂ)) =
      ∫ t in Set.Ioi (0 : ℝ), ∫ p in Set.Ioi (0 : ℝ), ∫ q in Set.Ioi (0 : ℝ), (((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (b + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t / r : ℝ) : ℂ) ^ (ν₂ + signShift (b + b)) * (Real.exp (-(Real.pi * (t / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (s - 1 / 2 - cP - (u₁ + u₂)) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ u₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ u₂ * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((p : ℝ) : ℂ) ^ (u₀ - (u₁ + u₂) - 1 - (δ : ℂ)) * ((q : ℝ) : ℂ) ^ (u₀ + cP + (u₁ + u₂) - 2 * s - 2 - (δ : ℂ)) *
          (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / q ^ 2)) : ℂ)) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hswap] with t ht hk
    exact hk ht
  rw [step4]

  have hbb : b + b = 0 := (by decide : ∀ b : ZMod 2, b + b = 0) b
  have hss0 : signShift (b + b) = 0 := by rw [hbb]; unfold signShift; simp
  have hδss : ((δ : ℕ) : ℂ) = signShift (b + a₀) := by
    rcases hδ with hδ0 | hδ1
    · have h0 : b + a₀ = 0 := by
        rw [add_comm]; have := hδpar; rw [hδ0, Nat.cast_zero] at this; exact this.symm
      rw [hδ0, h0]; unfold signShift; simp
    · have h1 : b + a₀ = 1 := by
        rw [add_comm]; have := hδpar; rw [hδ1, Nat.cast_one] at this; exact this.symm
      rw [hδ1, h1]; unfold signShift; simp
  have hδre : ((δ : ℕ) : ℂ).re = 0 ∨ ((δ : ℕ) : ℂ).re = 1 := by
    rcases hδ with h | h <;> simp [h]
  have hs1 := hsre (b + b)
  have hnre : ((n : ℕ) : ℂ) = 0 := by rw [hn, Nat.cast_zero]
  have habs : ∀ x : ℝ, -|x| ≤ x ∧ x ≤ |x| := fun x => ⟨neg_abs_le x, le_abs_self x⟩
  obtain ⟨hu1, hu2⟩ := habs u₀.re
  obtain ⟨hn11, hn12⟩ := habs ν₁.re
  obtain ⟨hn21, hn22⟩ := habs ν₂.re
  obtain ⟨hm11, hm12⟩ := habs u₁.re
  obtain ⟨hm21, hm22⟩ := habs u₂.re
  obtain ⟨hc1, hc2⟩ := habs cP.re
  have hR' : |u₀.re| + |ν₁.re| + |ν₂.re| + |u₁.re| + |u₂.re| + |cP.re| + 4 < s.re := by rw [hR] at hsR; exact hsR
  have hbal : (u₀ - (u₁ + u₂) - 1 - (δ : ℂ)) - (u₀ + cP + (u₁ + u₂) - 2 * s - 2 - (δ : ℂ)) =
      2 * (s - 1 / 2 - cP - (u₁ + u₂)) + 2 + (ν₁ + signShift (b + b)) + (ν₂ + signShift (b + b)) := by
    rw [hcP, hss0]; ring
  have hK8 := LanglandsTunnell.integral_mulConvGaussian_torusGauss_eq_GammaR_prod_div_of_balance
    (ν₁ + signShift (b + b)) (ν₂ + signShift (b + b)) u₁ u₂ (s - 1 / 2 - cP - (u₁ + u₂))
    (u₀ - (u₁ + u₂) - 1 - (δ : ℂ)) (u₀ + cP + (u₁ + u₂) - 2 * s - 2 - (δ : ℂ)) hbal
    (by rcases hs1 with h | h <;> rcases hδre with hd | hd <;> (simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, h, hd]; linarith))
    (by rcases hs1 with h | h <;> rcases hδre with hd | hd <;> (simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, h, hd]; linarith))
    (by rcases hs1 with h | h <;> rcases hδre with hd | hd <;> (simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, h, hd]; linarith))
    (by rcases hs1 with h | h <;> rcases hδre with hd | hd <;> (simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, h, hd]; linarith))
    (by rcases hs1 with h | h <;> rcases hδre with hd | hd <;> (simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, h, hd]; linarith))
    (by rcases hs1 with h | h <;> rcases hδre with hd | hd <;> (simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, h, hd]; linarith))
  rw [hK8]
  have hwre : 0 < (2 * s - cP - P₂.centralExponent + n + 1).re := by
    rw [hce, hnre]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re,
      Complex.zero_re, zero_mul, sub_zero, add_zero]
    linarith
  have hΓne : Complex.Gammaℝ (2 * s - cP - P₂.centralExponent + n + 1) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hwre
  have e0 : Complex.Gammaℝ ((u₀ - (u₁ + u₂) - 1 - (δ : ℂ)) - (u₀ + cP + (u₁ + u₂) - 2 * s - 2 - (δ : ℂ)) + u₁ + u₂) =
      Complex.Gammaℝ (2 * s - cP - P₂.centralExponent + n + 1) := by rw [hce, hnre]; congr 1; ring
  have e1 : Complex.Gammaℝ ((s - 1 / 2 - cP - (u₁ + u₂)) - (u₀ - (u₁ + u₂) - 1 - (δ : ℂ)) + (ν₁ + signShift (b + b))) =
      Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₀) + signShift (b + a₀))) := by rw [hss0, hδss, hcP]; congr 1; ring
  have e2 : Complex.Gammaℝ ((s - 1 / 2 - cP - (u₁ + u₂)) - (u₀ - (u₁ + u₂) - 1 - (δ : ℂ)) + (ν₂ + signShift (b + b))) =
      Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₀) + signShift (b + a₀))) := by rw [hss0, hδss, hcP]; congr 1; ring
  have e3 : Complex.Gammaℝ ((s - 1 / 2 - cP - (u₁ + u₂)) + 1 + (ν₁ + signShift (b + b)) + u₁) =
      Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₂) + signShift (b + b))) := by rw [hcP]; congr 1; ring
  have e4 : Complex.Gammaℝ ((s - 1 / 2 - cP - (u₁ + u₂)) + 1 + (ν₁ + signShift (b + b)) + u₂) =
      Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₁) + signShift (b + b))) := by rw [hcP]; congr 1; ring
  have e5 : Complex.Gammaℝ ((s - 1 / 2 - cP - (u₁ + u₂)) + 1 + (ν₂ + signShift (b + b)) + u₁) =
      Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₂) + signShift (b + b))) := by rw [hcP]; congr 1; ring
  have e6 : Complex.Gammaℝ ((s - 1 / 2 - cP - (u₁ + u₂)) + 1 + (ν₂ + signShift (b + b)) + u₂) =
      Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₁) + signShift (b + b))) := by rw [hcP]; congr 1; ring
  rw [e0, e1, e2, e3, e4, e5, e6]
  revert hΓne
  generalize Complex.Gammaℝ (2 * s - cP - P₂.centralExponent + n + 1) = G
  generalize Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₀) + signShift (b + a₀))) = A₁
  generalize Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₀) + signShift (b + a₀))) = A₂
  generalize Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₁) + signShift (b + b))) = B₁
  generalize Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₁) + signShift (b + b))) = B₂
  generalize Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₂) + signShift (b + b))) = B₃
  generalize Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₂) + signShift (b + b))) = B₄
  generalize ((-1 : ℂ) ^ (b.val + δ)) = ε
  intro hΓne
  have hfin : ∀ Y : ℂ, G * (2 * ε * ρ * (1 / 2 * Y / G)) = ε * ρ * Y := by
    intro Y
    rw [show G * (2 * ε * ρ * (1 / 2 * Y / G)) = ε * ρ * Y * (G / G) by ring, div_self hΓne, mul_one]
  rw [hfin]
  ring

end S_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_detPow_colHarmonic_eq_mul_prod_GammaR_of_evenPrincipal_of_weightZeroProfile
end P2MW
export P2MW.S_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_detPow_colHarmonic_eq_mul_prod_GammaR_of_evenPrincipal_of_weightZeroProfile (solution)
