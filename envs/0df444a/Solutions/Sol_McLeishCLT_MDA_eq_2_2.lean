-- Prove2me | solution 1 for McLeishCLT.MDA.eq_2_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:18:28.255262+00:00
-- url     : https://prove2.me/submissions/456784d2-cc72-45a8-b221-a6aa7ef96fcf

import Mathlib
import Definitions.Def_McLeishCLT_MDA_Setting

set_option autoImplicit false

namespace McLeishCLT.MDA.Eq22Proof

open MeasureTheory Filter Topology Finset Complex Set
open scoped ENNReal



theorem one_add_I_mul_ne_zero (t : ℝ) : (1 + I * (t : ℂ)) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem one_le_norm_one_add_I_mul (t : ℝ) : 1 ≤ ‖1 + I * (t : ℂ)‖ := by
  have h := Complex.abs_re_le_norm (1 + I * (t : ℂ))
  simpa using h

/-- `r'(t) = i + t - i/(1 + it)`. -/
theorem hasDerivAt_remR (t : ℝ) :
    HasDerivAt remR (I + (t : ℂ) - I / (1 + I * (t : ℂ))) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  have hI : HasDerivAt (fun s : ℝ => I * (s : ℂ)) (I * 1) t := h1.const_mul I
  have hsq : HasDerivAt (fun s : ℝ => (s : ℂ) ^ 2 / 2) ((2 : ℕ) * (t : ℂ) ^ (2 - 1) * 1 / 2) t :=
    (h1.pow 2).div_const 2
  have hlin : HasDerivAt (fun s : ℝ => 1 + I * (s : ℂ)) (0 + I * 1) t :=
    (hasDerivAt_const t (1 : ℂ)).add hI
  have hslit : (1 + I * (t : ℂ)) ∈ Complex.slitPlane := by
    left
    simp
  have hlog : HasDerivAt (fun s : ℝ => Complex.log (1 + I * (s : ℂ)))
      ((0 + I * 1) / (1 + I * (t : ℂ))) t := hlin.clog_real hslit
  have hall := (hI.add hsq).sub hlog
  have hfun : remR = fun s : ℝ => I * (s : ℂ) + (s : ℂ) ^ 2 / 2 - Complex.log (1 + I * (s : ℂ)) := by
    funext s
    rfl
  rw [hfun]
  have hall' : HasDerivAt
      (fun s : ℝ => I * (s : ℂ) + (s : ℂ) ^ 2 / 2 - Complex.log (1 + I * (s : ℂ)))
      (I * 1 + ((2 : ℕ) : ℂ) * (t : ℂ) ^ (2 - 1) * 1 / 2 - (0 + I * 1) / (1 + I * (t : ℂ))) t :=
    hall
  refine hall'.congr_deriv ?_
  rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one]
  push_cast
  ring

/-- `‖r'(t)‖ = t² / ‖1 + it‖ ≤ t²`. -/
theorem norm_deriv_remR_le (t : ℝ) : ‖I + (t : ℂ) - I / (1 + I * (t : ℂ))‖ ≤ t ^ 2 := by
  have hne := one_add_I_mul_ne_zero t
  have heq : I + (t : ℂ) - I / (1 + I * (t : ℂ)) = I * (t : ℂ) ^ 2 / (1 + I * (t : ℂ)) := by
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [heq, norm_div, norm_mul, Complex.norm_I, one_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  have h1 := one_le_norm_one_add_I_mul t
  calc t ^ 2 / ‖1 + I * (t : ℂ)‖ ≤ t ^ 2 / 1 :=
        div_le_div_of_nonneg_left (sq_nonneg t) one_pos h1
    _ = t ^ 2 := div_one _


/-- `‖r(x)‖ ≤ |x|³` for every real `x` (mean value inequality, `|r'(t)| ≤ t²`). -/
theorem norm_remR_le (x : ℝ) : ‖remR x‖ ≤ |x| ^ 3 := by
  have hmem0 : (0 : ℝ) ∈ Set.Icc (-|x|) |x| := ⟨by linarith [abs_nonneg x], abs_nonneg x⟩
  have hmemx : x ∈ Set.Icc (-|x|) |x| := ⟨neg_abs_le x, le_abs_self x⟩
  have hbound : ∀ t ∈ Set.Icc (-|x|) |x|, ‖I + (t : ℂ) - I / (1 + I * (t : ℂ))‖ ≤ x ^ 2 := by
    intro t ht
    refine (norm_deriv_remR_le t).trans ?_
    have : |t| ≤ |x| := abs_le.mpr ⟨ht.1, ht.2⟩
    nlinarith [abs_nonneg t, sq_abs t, sq_abs x]
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hasDerivAt_remR t).hasDerivWithinAt) hbound (convex_Icc _ _) hmem0 hmemx
  have h0 : remR 0 = 0 := by simp [remR]
  rw [h0, sub_zero, sub_zero, Real.norm_eq_abs] at hmvt
  calc ‖remR x‖ ≤ x ^ 2 * |x| := hmvt
    _ = |x| ^ 3 := by rw [← sq_abs]; ring

/-- `e^{ix} = (1 + ix) exp(-x²/2 + r(x))`. -/
theorem exp_I_eq (x : ℝ) :
    Complex.exp (I * (x : ℂ)) = (1 + I * (x : ℂ)) * Complex.exp (-(x : ℂ) ^ 2 / 2 + remR x) := by
  have hne := one_add_I_mul_ne_zero x
  have h : -(x : ℂ) ^ 2 / 2 + remR x = I * (x : ℂ) - Complex.log (1 + I * (x : ℂ)) := by
    unfold remR
    ring
  rw [h, Complex.exp_sub, Complex.exp_log hne]
  field_simp

theorem measurable_remR : Measurable remR := by
  have h : remR = fun x : ℝ => I * (x : ℂ) + (x : ℂ) ^ 2 / 2 - Complex.log (1 + I * (x : ℂ)) := by
    funext x
    rfl
  rw [h]
  exact ((measurable_const.mul Complex.measurable_ofReal).add
    ((Complex.measurable_ofReal.pow_const 2).div_const 2)).sub
    (Complex.measurable_log.comp (measurable_const.add (measurable_const.mul Complex.measurable_ofReal)))

variable {Ω : Type*}

/-- `T_n U_n = ∏_j e^{i t X_{n,j}}`. -/
theorem prodT_mul_prodU (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ) (t : ℝ) (n : ℕ) (ω : Ω) :
    prodT k X t n ω * prodU k X t n ω =
      ∏ j ∈ range (k n), Complex.exp (I * ((X n j ω * t : ℝ) : ℂ)) := by
  unfold prodT prodU
  have hsum : -(t : ℂ) ^ 2 / 2 * ∑ j ∈ range (k n), (X n j ω : ℂ) ^ 2
      + ∑ j ∈ range (k n), remR (X n j ω * t)
      = ∑ j ∈ range (k n), (-((X n j ω * t : ℝ) : ℂ) ^ 2 / 2 + remR (X n j ω * t)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [hsum, Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [exp_I_eq]
  congr 1
  push_cast
  ring

theorem norm_prodT_mul_prodU (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ) (t : ℝ) (n : ℕ) (ω : Ω) :
    ‖prodT k X t n ω * prodU k X t n ω‖ = 1 := by
  rw [prodT_mul_prodU, norm_prod]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The exponent gap `z_n = -t²/2 - log U_n`. -/
noncomputable def zfun (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ) (t : ℝ) (n : ℕ) (ω : Ω) : ℂ :=
  -(t : ℂ) ^ 2 / 2 - (-(t : ℂ) ^ 2 / 2 * ∑ j ∈ range (k n), (X n j ω : ℂ) ^ 2
    + ∑ j ∈ range (k n), remR (X n j ω * t))

/-- `T_n (U_n - e^{-t²/2}) = T_n U_n (1 - e^{z_n})`. -/
theorem W_eq (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ) (t : ℝ) (n : ℕ) (ω : Ω) :
    prodT k X t n ω * (prodU k X t n ω - Complex.exp (-(t : ℂ) ^ 2 / 2))
      = prodT k X t n ω * prodU k X t n ω * (1 - Complex.exp (zfun k X t n ω)) := by
  have hc : Complex.exp (-(t : ℂ) ^ 2 / 2) = prodU k X t n ω * Complex.exp (zfun k X t n ω) := by
    unfold prodU zfun
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hc]
  ring

theorem norm_W_eq (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ) (t : ℝ) (n : ℕ) (ω : Ω) :
    ‖prodT k X t n ω * (prodU k X t n ω - Complex.exp (-(t : ℂ) ^ 2 / 2))‖
      = ‖Complex.exp (zfun k X t n ω) - 1‖ := by
  rw [W_eq, norm_mul, norm_prodT_mul_prodU, one_mul, norm_sub_rev]

theorem norm_W_le (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ) (t : ℝ) (n : ℕ) (ω : Ω) :
    ‖prodT k X t n ω * (prodU k X t n ω - Complex.exp (-(t : ℂ) ^ 2 / 2))‖
      ≤ 1 + ‖Complex.exp (-(t : ℂ) ^ 2 / 2)‖ * ‖prodT k X t n ω‖ := by
  rw [mul_sub]
  calc ‖prodT k X t n ω * prodU k X t n ω - prodT k X t n ω * Complex.exp (-(t : ℂ) ^ 2 / 2)‖
      ≤ ‖prodT k X t n ω * prodU k X t n ω‖
        + ‖prodT k X t n ω * Complex.exp (-(t : ℂ) ^ 2 / 2)‖ := norm_sub_le _ _
    _ = 1 + ‖Complex.exp (-(t : ℂ) ^ 2 / 2)‖ * ‖prodT k X t n ω‖ := by
        rw [norm_prodT_mul_prodU, norm_mul, mul_comm]

theorem abs_le_maxAbs (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (j : ℕ) (hj : j < k n) :
    |X n j ω| ≤ maxAbs k X n ω :=
  le_ciSup (f := fun i : Fin (k n) => |X n i ω|) (Finite.bddAbove_range _) ⟨j, hj⟩

/-- `‖z_n‖ ≤ (t²/2)|Σ X² - 1| + |t|³ (max |X|) Σ X²`. -/
theorem norm_zfun_le (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ) (t : ℝ) (n : ℕ) (ω : Ω) :
    ‖zfun k X t n ω‖ ≤ t ^ 2 / 2 * |sumSq k X n ω - 1|
      + |t| ^ 3 * (maxAbs k X n ω * sumSq k X n ω) := by
  have hz : zfun k X t n ω = ((t ^ 2 / 2 * (sumSq k X n ω - 1) : ℝ) : ℂ)
      - ∑ j ∈ range (k n), remR (X n j ω * t) := by
    unfold zfun sumSq
    push_cast
    ring
  rw [hz]
  have h1 : ‖((t ^ 2 / 2 * (sumSq k X n ω - 1) : ℝ) : ℂ)‖ = t ^ 2 / 2 * |sumSq k X n ω - 1| := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
  have h2 : ‖∑ j ∈ range (k n), remR (X n j ω * t)‖ ≤ ∑ j ∈ range (k n), |X n j ω * t| ^ 3 :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_remR_le _)
  have h3 : ∑ j ∈ range (k n), |X n j ω * t| ^ 3 ≤ |t| ^ 3 * (maxAbs k X n ω * sumSq k X n ω) := by
    unfold sumSq
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hle := abs_le_maxAbs k X n ω j (Finset.mem_range.mp hj)
    have hx2 : 0 ≤ X n j ω ^ 2 := sq_nonneg _
    have : |X n j ω * t| ^ 3 = |t| ^ 3 * (|X n j ω| * X n j ω ^ 2) := by
      rw [abs_mul, mul_pow, ← sq_abs (X n j ω)]
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle hx2) (by positivity)
  calc ‖((t ^ 2 / 2 * (sumSq k X n ω - 1) : ℝ) : ℂ) - ∑ j ∈ range (k n), remR (X n j ω * t)‖
      ≤ ‖((t ^ 2 / 2 * (sumSq k X n ω - 1) : ℝ) : ℂ)‖ + ‖∑ j ∈ range (k n), remR (X n j ω * t)‖ :=
        norm_sub_le _ _
    _ ≤ t ^ 2 / 2 * |sumSq k X n ω - 1| + |t| ^ 3 * (maxAbs k X n ω * sumSq k X n ω) := by
        rw [h1]
        linarith

end McLeishCLT.MDA.Eq22Proof

open MeasureTheory ProbabilityTheory Filter Topology Finset Complex Set
  McLeishCLT.MDA McLeishCLT.MDA.Eq22Proof
open scoped ENNReal NNReal

theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ)
    (hXm : ∀ n, ∀ j < k n, Measurable (X n j)) (t : ℝ)
    (hb : UniformIntegrable (fun n => prodT k X t n) 1 P)
    (hc : TendstoInMeasure P (fun n => sumSq k X n) atTop (fun _ => 1))
    (hd : TendstoInMeasure P (fun n => maxAbs k X n) atTop (fun _ => 0)) :
    Tendsto (fun n => eLpNorm (fun ω => prodT k X t n ω *
      (prodU k X t n ω - Complex.exp (-(t : ℂ) ^ 2 / 2))) 1 P) atTop (𝓝 0) := by
  set c : ℂ := Complex.exp (-(t : ℂ) ^ 2 / 2) with hcdef
  set W : ℕ → Ω → ℂ := fun n ω => prodT k X t n ω * (prodU k X t n ω - c) with hWdef
  -- Measurability.
  have hTm : ∀ n, Measurable (prodT k X t n) := by
    intro n
    unfold prodT
    exact Finset.measurable_prod _ fun j hj => measurable_const.add (measurable_const.mul
      (Complex.measurable_ofReal.comp (hXm n j (Finset.mem_range.mp hj))))
  have hUm : ∀ n, Measurable (prodU k X t n) := by
    intro n
    unfold prodU
    refine Complex.measurable_exp.comp ((measurable_const.mul (Finset.measurable_sum _ fun j hj =>
      (Complex.measurable_ofReal.comp (hXm n j (Finset.mem_range.mp hj))).pow_const 2)).add
      (Finset.measurable_sum _ fun j hj => measurable_remR.comp
        ((hXm n j (Finset.mem_range.mp hj)).mul_const t)))
  have hWm : ∀ n, AEStronglyMeasurable (W n) P := fun n =>
    ((hTm n).mul ((hUm n).sub measurable_const)).aestronglyMeasurable
  -- Uniform integrability: `‖W_n‖ ≤ 1 + ‖c‖ ‖T_n‖`.
  have hWb : ∀ n ω, ‖W n ω‖ₑ ≤ 1 + ‖c‖ₑ * ‖prodT k X t n ω‖ₑ := by
    intro n ω
    have h := norm_W_le k X t n ω
    rw [← hcdef] at h
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_add zero_le_one (by positivity)]
    exact ENNReal.ofReal_le_ofReal h
  have hW_ui : UnifIntegrable W 1 P := by
    intro ε hε
    have hc0 : 0 < ‖c‖ + 1 := by positivity
    obtain ⟨δ₁, hδ₁, hT⟩ := hb.unifIntegrable (by positivity : 0 < ε / 2 / (‖c‖ + 1))
    refine ⟨min δ₁ (ε / 2), lt_min hδ₁ (by positivity), fun n s hs hPs => ?_⟩
    have hT' := hT n s hs (hPs.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
    rw [eLpNorm_one_eq_lintegral_enorm] at hT' ⊢
    simp_rw [enorm_indicator_eq_indicator_enorm] at hT' ⊢
    rw [lintegral_indicator hs] at hT' ⊢
    calc ∫⁻ ω in s, ‖W n ω‖ₑ ∂P ≤ ∫⁻ ω in s, (1 + ‖c‖ₑ * ‖prodT k X t n ω‖ₑ) ∂P :=
          lintegral_mono fun ω => hWb n ω
      _ = P s + ‖c‖ₑ * ∫⁻ ω in s, ‖prodT k X t n ω‖ₑ ∂P := by
          rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply
            MeasurableSet.univ, univ_inter, one_mul, lintegral_const_mul' _ _ enorm_ne_top]
      _ ≤ ENNReal.ofReal (ε / 2) + ‖c‖ₑ * ENNReal.ofReal (ε / 2 / (‖c‖ + 1)) :=
          add_le_add (hPs.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _)))
            (mul_le_mul' le_rfl hT')
      _ ≤ ENNReal.ofReal ε := by
          rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have : ‖c‖ * (ε / 2 / (‖c‖ + 1)) ≤ ε / 2 := by
            rw [mul_div_assoc', div_le_iff₀ hc0]
            nlinarith [norm_nonneg c]
          linarith
  -- Convergence in measure of `W_n` to `0`.
  have hW_meas : TendstoInMeasure P W atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    set δ : ℝ := min 1 (ε / 4) with hδdef
    have hδ : 0 < δ := lt_min one_pos (by positivity)
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδε : δ ≤ ε / 4 := min_le_right _ _
    set δ₁ : ℝ := min 1 (δ / (t ^ 2 + 1)) with hδ₁def
    set δ₂ : ℝ := δ / (4 * (|t| ^ 3 + 1)) with hδ₂def
    have hδ₁ : 0 < δ₁ := lt_min one_pos (by positivity)
    have hδ₂ : 0 < δ₂ := by positivity
    have hcd := (tendstoInMeasure_iff_dist.mp hc) δ₁ hδ₁
    have hdd := (tendstoInMeasure_iff_dist.mp hd) δ₂ hδ₂
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hcd.add hdd) (fun n => zero_le) (fun n => ?_)
    refine (measure_mono ?_).trans (measure_union_le _ _)
    intro ω hω
    simp only [mem_ofPred_eq, sub_zero] at hω
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_le, Real.dist_eq] at hnot
    obtain ⟨h1, h2⟩ := hnot
    have hs0 : 0 ≤ sumSq k X n ω := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hs2 : sumSq k X n ω ≤ 2 := by
      have := (abs_lt.mp (lt_of_lt_of_le h1 (min_le_left _ _))).2
      linarith
    have hA : t ^ 2 / 2 * |sumSq k X n ω - 1| ≤ δ / 2 := by
      have hle : |sumSq k X n ω - 1| ≤ δ / (t ^ 2 + 1) := h1.le.trans (min_le_right _ _)
      have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
      calc t ^ 2 / 2 * |sumSq k X n ω - 1| ≤ t ^ 2 / 2 * (δ / (t ^ 2 + 1)) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ ≤ δ / 2 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
    have hB : |t| ^ 3 * (maxAbs k X n ω * sumSq k X n ω) ≤ δ / 2 := by
      have hm : maxAbs k X n ω * sumSq k X n ω ≤ δ₂ * 2 := by
        have := le_abs_self (maxAbs k X n ω)
        nlinarith
      have ht3 : 0 ≤ |t| ^ 3 := by positivity
      calc |t| ^ 3 * (maxAbs k X n ω * sumSq k X n ω) ≤ |t| ^ 3 * (δ₂ * 2) :=
            mul_le_mul_of_nonneg_left hm ht3
        _ = δ / 2 * (|t| ^ 3 / (|t| ^ 3 + 1)) := by
            rw [hδ₂def]
            field_simp
            ring
        _ ≤ δ / 2 := by
            have : |t| ^ 3 / (|t| ^ 3 + 1) ≤ 1 := by
              rw [div_le_one (by positivity)]
              linarith
            nlinarith
    have hz : ‖zfun k X t n ω‖ ≤ δ := by
      have := norm_zfun_le k X t n ω
      linarith
    have hW : ‖W n ω‖ ≤ 2 * δ := by
      simp only [hWdef, hcdef]
      rw [norm_W_eq]
      calc ‖Complex.exp (zfun k X t n ω) - 1‖ ≤ 2 * ‖zfun k X t n ω‖ :=
            Complex.norm_exp_sub_one_le (hz.trans hδ1)
        _ ≤ 2 * δ := by linarith
    linarith
  -- Vitali.
  have hV := tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top hWm
    (memLp_const (0 : ℂ)) hW_ui hW_meas
  have hfun : ∀ n, (W n - fun _ => (0 : ℂ)) = W n := fun n => by
    funext ω
    simp
  simp only [hfun] at hV
  exact hV
