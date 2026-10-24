-- Prove2me | solution 1 for K24.Global.FlatTorus.scalarSharpnessIngredient
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:01:35.410667+00:00
-- url     : https://prove2.me/submissions/e2091deb-291f-4b86-8270-2b10213bb227

import Definitions.Def_K24GlobalStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Topology
open scoped NNReal ENNReal ContDiff

namespace K24.Global.FlatTorus

private theorem oscillatingScalar_quotientMap (alpha : ℝ) (n : ℕ) (x : FourSpace) :
    oscillatingScalar alpha n (quotientMap x) = liftedOscillation alpha n (x 0) := by
  simp only [oscillatingScalar, quotientMap, liftedOscillation]
  rw [← Circle.exp_nsmul]
  simp only [Circle.coe_exp, nsmul_eq_mul, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.add_im,
    Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    Complex.I_re, mul_one, mul_zero, zero_add, add_zero]

private theorem hasDerivAt_liftedOscillation (alpha : ℝ) (n : ℕ) (r : ℝ) :
    HasDerivAt (liftedOscillation alpha n)
      (amplitude alpha n * (n : ℝ) * Real.cos ((n : ℝ) * r)) r := by
  change HasDerivAt (fun y => amplitude alpha n * Real.sin ((n : ℝ) * y)) _ r
  simpa [Function.comp_def, mul_assoc, mul_comm, mul_left_comm] using
    (((Real.hasDerivAt_sin ((n : ℝ) * r)).comp r
      ((hasDerivAt_id r).const_mul (n : ℝ))).const_mul (amplitude alpha n))

private theorem deriv_liftedOscillation (alpha : ℝ) (n : ℕ) :
    deriv (liftedOscillation alpha n) =
      fun r => amplitude alpha n * (n : ℝ) * Real.cos ((n : ℝ) * r) := by
  funext r
  exact (hasDerivAt_liftedOscillation alpha n r).deriv

private theorem deriv_twice_liftedOscillation (alpha : ℝ) (n : ℕ) :
    deriv (deriv (liftedOscillation alpha n)) =
      fun r => -(amplitude alpha n * (n : ℝ)^2) * Real.sin ((n : ℝ) * r) := by
  rw [deriv_liftedOscillation]
  funext r
  convert (((Real.hasDerivAt_cos ((n : ℝ) * r)).comp r
    ((hasDerivAt_id r).const_mul (n : ℝ))).const_mul
      (amplitude alpha n * (n : ℝ))).deriv using 1 <;> simp [Function.comp_def] <;> ring

/-- The first exact prescribed defect coefficient restricted to the first coordinate line. -/
private def defectLine (alpha : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  expectedDefectCoefficients alpha n (r • basisVector 0) 0

private theorem defectLine_eq (alpha : ℝ) (n : ℕ) :
    defectLine alpha n = fun r =>
      amplitude alpha n * (1 + (n : ℝ)^2 / 2) * Real.sin ((n : ℝ) * r) := by
  funext r
  simp [defectLine, expectedDefectCoefficients, basisVector,
    deriv_twice_liftedOscillation, liftedOscillation]
  ring

private theorem deriv_defectLine (alpha : ℝ) (n : ℕ) :
    deriv (defectLine alpha n) = fun r =>
      amplitude alpha n * (1 + (n : ℝ)^2 / 2) * (n : ℝ) *
        Real.cos ((n : ℝ) * r) := by
  rw [defectLine_eq]
  funext r
  convert (((Real.hasDerivAt_sin ((n : ℝ) * r)).comp r
    ((hasDerivAt_id r).const_mul (n : ℝ))).const_mul
      (amplitude alpha n * (1 + (n : ℝ)^2 / 2))).deriv using 1 <;>
      (try dsimp only [Function.comp_def]) <;> ring

private theorem amplitude_pos (alpha : ℝ) {n : ℕ} (hn : 0 < n) :
    0 < amplitude alpha n :=
  Real.rpow_pos_of_pos (by exact_mod_cast hn) _

private theorem amplitude_scaling (alpha : ℝ) {n : ℕ} (hn : 0 < n) :
    amplitude alpha n * Real.rpow (n : ℝ) alpha = 1 / (n : ℝ)^3 := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  simp only [amplitude, Real.rpow_eq_pow]
  rw [← Real.rpow_add hn']
  convert Real.rpow_neg hn'.le (3 : ℝ) using 1 <;> norm_num <;> ring

/-- A concrete Hölder difference quotient, not a new section norm. -/
private def defectHolderWitness (alpha : ℝ) (n : ℕ) : ℝ :=
  |deriv (defectLine alpha n) 0 - deriv (defectLine alpha n) (Real.pi / n)| /
    Real.rpow |(0 : ℝ) - Real.pi / n| alpha

private theorem defectHolderWitness_eq (alpha : ℝ) {n : ℕ} (hn : 0 < n) :
    defectHolderWitness alpha n =
      (1 + 2 / (n : ℝ)^2) * Real.rpow Real.pi (-alpha) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcoef : 0 ≤ amplitude alpha n * (1 + (n : ℝ)^2 / 2) * (n : ℝ) := by
    have := (amplitude_pos alpha hn).le
    positivity
  rw [defectHolderWitness, deriv_defectLine]
  simp only [mul_zero, Real.cos_zero, mul_one]
  rw [mul_div_cancel₀ _ hn'.ne', Real.cos_pi]
  rw [show amplitude alpha n * (1 + (n : ℝ)^2 / 2) * (n : ℝ) -
      amplitude alpha n * (1 + (n : ℝ)^2 / 2) * (n : ℝ) * -1 =
      2 * (amplitude alpha n * (1 + (n : ℝ)^2 / 2) * (n : ℝ)) by ring]
  rw [abs_of_nonneg (mul_nonneg (by norm_num) hcoef), zero_sub, abs_neg,
    abs_of_pos (div_pos hpi hn')]
  simp only [Real.rpow_eq_pow]
  rw [Real.div_rpow hpi.le hn'.le,
    Real.rpow_neg hpi.le]
  have hscale := amplitude_scaling alpha hn
  simp only [Real.rpow_eq_pow] at hscale
  have hnpow : Real.rpow (n : ℝ) alpha ≠ 0 :=
    (Real.rpow_pos_of_pos hn' alpha).ne'
  have hpipow : Real.rpow Real.pi alpha ≠ 0 :=
    (Real.rpow_pos_of_pos hpi alpha).ne'
  simp only [Real.rpow_eq_pow] at hnpow hpipow
  field_simp [hn'.ne', hnpow, hpipow] at hscale ⊢
  linear_combination ((n : ℝ)^2 + 2) * hscale

private theorem defectHolderWitness_lower (alpha : ℝ) {n : ℕ} (hn : 0 < n) :
    Real.rpow Real.pi (-alpha) ≤ defectHolderWitness alpha n := by
  rw [defectHolderWitness_eq alpha hn]
  simp only [Real.rpow_eq_pow]
  have hpi := (Real.rpow_pos_of_pos Real.pi_pos (-alpha)).le
  have hfrac : 0 ≤ 2 / (n : ℝ)^2 := by positivity
  nlinarith

private theorem iteratedDeriv_liftedOscillation (alpha : ℝ) (n k : ℕ) :
    iteratedDeriv k (liftedOscillation alpha n) = fun x =>
      amplitude alpha n * (n : ℝ)^k * iteratedDeriv k Real.sin ((n : ℝ) * x) := by
  funext x
  change iteratedDeriv k (fun y => amplitude alpha n * Real.sin ((n : ℝ) * y)) x = _
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_mul Real.contDiff_sin]
  simp only
  ring

private theorem abs_iteratedDeriv_liftedOscillation_le (alpha : ℝ) {n : ℕ}
    (hn : 0 < n) (k : ℕ) (x : ℝ) :
    |iteratedDeriv k (liftedOscillation alpha n) x| ≤
      amplitude alpha n * (n : ℝ)^k := by
  rw [iteratedDeriv_liftedOscillation, abs_mul,
    abs_of_nonneg (mul_nonneg (amplitude_pos alpha hn).le (by positivity))]
  exact mul_le_of_le_one_right
    (mul_nonneg (amplitude_pos alpha hn).le (by positivity))
    (Real.abs_iteratedDeriv_sin_le_one k _)

private theorem holderWith_iteratedDeriv_sin (alpha : ℝ≥0) (ha : alpha ≤ 1) (k : ℕ) :
    HolderWith 2 alpha (iteratedDeriv k Real.sin) := by
  have hzero : HolderWith 2 0 (iteratedDeriv k Real.sin) := by
    intro x y
    simp only [NNReal.coe_zero, ENNReal.rpow_zero, mul_one]
    rw [edist_dist]
    norm_num only [ENNReal.coe_ofNat]
    rw [← ENNReal.ofReal_ofNat]
    apply ENNReal.ofReal_le_ofReal
    change |iteratedDeriv k Real.sin x - iteratedDeriv k Real.sin y| ≤ 2
    exact (abs_sub _ _).trans (by
      linarith [Real.abs_iteratedDeriv_sin_le_one k x,
        Real.abs_iteratedDeriv_sin_le_one k y])
  have hone : LipschitzWith 1 (iteratedDeriv k Real.sin) := by
    apply lipschitzWith_of_nnnorm_deriv_le (Real.differentiable_iteratedDeriv_sin k)
    intro x
    change |deriv (iteratedDeriv k Real.sin) x| ≤ (1 : ℝ)
    rw [← iteratedDeriv_succ]
    exact Real.abs_iteratedDeriv_sin_le_one _ _
  simpa using hzero.of_le_of_le hone.holderWith (bot_le : 0 ≤ alpha) ha

private theorem holderWith_iteratedDeriv_liftedOscillation (alpha : ℝ≥0)
    (ha : alpha ≤ 1) (n k : ℕ) :
    HolderWith ((2 * (n : ℝ≥0) ^ (alpha : ℝ)) *
      ‖amplitude alpha n * (n : ℝ)^k‖₊) alpha
      (iteratedDeriv k (liftedOscillation alpha n)) := by
  have hscale : LipschitzWith (n : ℝ≥0) (fun x : ℝ => (n : ℝ) * x) := by
    apply lipschitzWith_of_nnnorm_deriv_le (by fun_prop)
    intro x
    simp [deriv_const_mul_id, Real.nnnorm_of_nonneg (Nat.cast_nonneg n)]
  have h := ((holderWith_iteratedDeriv_sin alpha ha k).comp hscale.holderWith).smul
    (amplitude alpha n * (n : ℝ)^k)
  intro x y
  have hxy := h x y
  simpa only [iteratedDeriv_liftedOscillation, Function.comp_def, mul_one,
    Pi.smul_apply, smul_eq_mul] using hxy

/-- A bound on the existing full scalar coordinate Hölder norm from literal derivatives. -/
private theorem scalar_coordinateHolderENorm_le {f : ℝ → ℝ} (k : ℕ) (alpha B D : ℝ≥0)
    (hsup : ∀ j ≤ k, ∀ x : ℝ, |iteratedDeriv j f x| ≤ B)
    (hholder : HolderWith D alpha (iteratedDeriv k f)) :
    coordinateHolderENorm k alpha Set.univ f ≤ (k + 1 : ℕ) * (B : ℝ≥0∞) + D := by
  unfold coordinateHolderENorm
  apply add_le_add
  · calc
      ∑ j ∈ Finset.range (k + 1), derivativeENorm j Set.univ f ≤
          ∑ j ∈ Finset.range (k + 1), (B : ℝ≥0∞) := by
        apply Finset.sum_le_sum
        intro j hj
        unfold derivativeENorm
        apply iSup_le
        intro x
        apply ENNReal.coe_le_coe.mpr
        change ‖iteratedFDerivWithin ℝ j f Set.univ (x : ℝ)‖ ≤ (B : ℝ)
        rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        exact hsup j (by simpa using Finset.mem_range.mp hj) x
      _ = _ := by simp
  · apply HolderWith.eHolderNorm_le
    intro x y
    simpa only [iteratedFDerivWithin_univ, iteratedFDeriv_eq_equiv_comp,
      Function.comp_apply, LinearIsometryEquiv.edist_map, Subtype.edist_eq] using
      hholder (x : ℝ) (y : ℝ)

private theorem coordinateHolderENorm_liftedOscillation_le (alpha : ℝ≥0)
    (ha : alpha ≤ 1) {n : ℕ} (hn : 0 < n) (k : ℕ) :
    coordinateHolderENorm k alpha Set.univ (liftedOscillation alpha n) ≤
      ENNReal.ofReal (((k : ℝ) + 1) * (amplitude alpha n * (n : ℝ)^k) +
        2 * Real.rpow (n : ℝ) alpha * (amplitude alpha n * (n : ℝ)^k)) := by
  have hA := (amplitude_pos (alpha : ℝ) hn).le
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  let B : ℝ≥0 := ⟨amplitude alpha n * (n : ℝ)^k, by positivity⟩
  let D : ℝ≥0 := (2 * (n : ℝ≥0) ^ (alpha : ℝ)) *
    ‖amplitude alpha n * (n : ℝ)^k‖₊
  have hs : ∀ j ≤ k, ∀ x : ℝ, |iteratedDeriv j (liftedOscillation alpha n) x| ≤ B := by
    intro j hj x
    exact (abs_iteratedDeriv_liftedOscillation_le alpha hn j x).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 hj) hA)
  have hb := scalar_coordinateHolderENorm_le k alpha B D hs
    (holderWith_iteratedDeriv_liftedOscillation alpha ha n k)
  have hd : (D : ℝ) = 2 * Real.rpow (n : ℝ) alpha *
      (amplitude alpha n * (n : ℝ)^k) := by
    simp only [D, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_rpow, NNReal.coe_natCast,
      coe_nnnorm, Real.norm_eq_abs, Real.rpow_eq_pow]
    rw [abs_of_nonneg (mul_nonneg hA (by positivity))]
  have heq : ENNReal.ofReal (((k : ℝ) + 1) * (amplitude alpha n * (n : ℝ)^k) +
      2 * Real.rpow (n : ℝ) alpha * (amplitude alpha n * (n : ℝ)^k)) =
      (k + 1 : ℕ) * (B : ℝ≥0∞) + D := by
    rw [← hd]
    change ENNReal.ofReal (((k : ℝ) + 1) * (B : ℝ) + (D : ℝ)) = _
    rw [ENNReal.ofReal_add (by positivity) D.coe_nonneg,
      ENNReal.ofReal_mul (by positivity)]
    simp [ENNReal.ofReal_add (Nat.cast_nonneg k) zero_le_one]
  rw [heq]
  exact hb

private theorem amplitude_cubic_scaling (alpha : ℝ) {n : ℕ} (hn : 0 < n) :
    (amplitude alpha n * (n : ℝ)^3) * (n : ℝ)^alpha = 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h := amplitude_scaling alpha hn
  simp only [Real.rpow_eq_pow] at h
  field_simp [hn'] at h
  nlinarith [h]

private theorem scalar_C3alpha_bound (alpha : ℝ≥0) (ha : alpha ≤ 1)
    {n : ℕ} (hn : 0 < n) :
    coordinateHolderENorm 3 alpha Set.univ (liftedOscillation alpha n) ≤ 6 := by
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hp : 1 ≤ (n : ℝ)^(alpha : ℝ) := Real.one_le_rpow hn1 alpha.coe_nonneg
  have hB : 0 ≤ amplitude alpha n * (n : ℝ)^3 := by
    exact mul_nonneg (amplitude_pos alpha hn).le (by positivity)
  have heq := amplitude_cubic_scaling (alpha : ℝ) hn
  have hb : amplitude alpha n * (n : ℝ)^3 ≤ 1 := by
    calc
      _ ≤ (amplitude alpha n * (n : ℝ)^3) * (n : ℝ)^(alpha : ℝ) :=
        le_mul_of_one_le_right hB hp
      _ = 1 := heq
  apply (coordinateHolderENorm_liftedOscillation_le alpha ha hn 3).trans
  rw [← ENNReal.ofReal_ofNat]
  apply ENNReal.ofReal_le_ofReal
  simp only [Nat.cast_ofNat, Real.rpow_eq_pow]
  nlinarith

private theorem scalar_C2alpha_bound (alpha : ℝ≥0) (ha : alpha ≤ 1)
    {n : ℕ} (hn : 0 < n) :
    coordinateHolderENorm 2 alpha Set.univ (liftedOscillation alpha n) ≤
      ENNReal.ofReal (5 / (n : ℝ)) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hp : 1 ≤ (n : ℝ)^(alpha : ℝ) := Real.one_le_rpow hn1 alpha.coe_nonneg
  have hB : 0 ≤ amplitude alpha n * (n : ℝ)^2 := by
    exact mul_nonneg (amplitude_pos alpha hn).le (by positivity)
  have heq : (amplitude alpha n * (n : ℝ)^2) * (n : ℝ)^(alpha : ℝ) = 1 / (n : ℝ) := by
    apply (eq_div_iff hn'.ne').mpr
    convert amplitude_cubic_scaling (alpha : ℝ) hn using 1 <;> ring
  have hb : amplitude alpha n * (n : ℝ)^2 ≤ 1 / (n : ℝ) := by
    calc
      _ ≤ (amplitude alpha n * (n : ℝ)^2) * (n : ℝ)^(alpha : ℝ) :=
        le_mul_of_one_le_right hB hp
      _ = _ := heq
  apply (coordinateHolderENorm_liftedOscillation_le alpha ha hn 2).trans
  apply ENNReal.ofReal_le_ofReal
  simp only [Nat.cast_ofNat, Real.rpow_eq_pow]
  simp only [div_eq_mul_inv, one_mul] at heq hb ⊢
  nlinarith

private theorem scalar_C2alpha_tendsto_zero (alpha : ℝ≥0) (ha : alpha ≤ 1) :
    Tendsto (fun n : ℕ =>
      (coordinateHolderENorm 2 alpha Set.univ (liftedOscillation alpha n)).toReal)
      atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
    _ (tendsto_const_div_atTop_nhds_zero_nat (5 : ℝ))
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (scalar_C2alpha_bound alpha ha hn)

private theorem liftedOscillation_smooth (alpha : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (liftedOscillation alpha n) := by
  unfold liftedOscillation
  fun_prop

private theorem liftedOscillation_zero (alpha : ℝ) : liftedOscillation alpha 0 = 0 := by
  funext x
  simp [liftedOscillation]

private theorem scalar_coordinateHolderENorm_zero (k : ℕ) (alpha : ℝ≥0) :
    coordinateHolderENorm k alpha Set.univ (0 : ℝ → ℝ) = 0 := by
  simp [coordinateHolderENorm, derivativeENorm, iteratedFDerivWithin_zero]
  exact eHolderNorm_const _ _ _

private theorem scalar_C3alpha_bound_all (alpha : ℝ≥0) (ha : alpha ≤ 1) (n : ℕ) :
    coordinateHolderENorm 3 alpha Set.univ (liftedOscillation alpha n) ≤ 6 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [liftedOscillation_zero, scalar_coordinateHolderENorm_zero]
    exact zero_le
  · exact scalar_C3alpha_bound alpha ha hn

private theorem scalar_C2alpha_finite (alpha : ℝ≥0) (ha : alpha ≤ 1) (n : ℕ) :
    coordinateHolderENorm 2 alpha Set.univ (liftedOscillation alpha n) < ⊤ := by
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [liftedOscillation_zero, scalar_coordinateHolderENorm_zero]
    exact ENNReal.zero_lt_top
  · exact (scalar_C2alpha_bound alpha ha hn).trans_lt ENNReal.ofReal_lt_top

/-- No constant controls the exact defect witness by the prescribed scalar C²α norm. -/
private theorem no_scalar_shifted_bound (alpha : ℝ≥0) (ha : alpha ≤ 1) :
    ¬ (∃ K : ℝ, ∀ n : ℕ, 2 ≤ n →
      defectHolderWitness alpha n ≤ K *
        (coordinateHolderENorm 2 alpha Set.univ (liftedOscillation alpha n)).toReal) := by
  rintro ⟨K, hK⟩
  have hlim : Tendsto (fun n : ℕ => K *
      (coordinateHolderENorm 2 alpha Set.univ (liftedOscillation alpha n)).toReal)
      atTop (𝓝 0) := by
    simpa using (scalar_C2alpha_tendsto_zero alpha ha).const_mul K
  have hle : Real.rpow Real.pi (-(alpha : ℝ)) ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact (defectHolderWitness_lower alpha (by omega)).trans (hK n hn)
  exact (Real.rpow_pos_of_pos Real.pi_pos (-(alpha : ℝ))).not_ge hle

end K24.Global.FlatTorus

open K24.Global K24.Global.FlatTorus

theorem solution :
  ∀ alpha : HolderExponent,
    (∀ (n : ℕ) (x : FourSpace),
      oscillatingScalar alpha.value n (quotientMap x) =
        liftedOscillation alpha.value n (x 0)) ∧
    (∀ n : ℕ,
      ContDiff ℝ ∞ (liftedOscillation alpha.value n) ∧
      BigHolderOn 2 alpha.value Set.univ (liftedOscillation alpha.value n) ∧
      BigHolderOn 3 alpha.value Set.univ (liftedOscillation alpha.value n) ∧
      coordinateHolderENorm 3 alpha.value Set.univ (liftedOscillation alpha.value n) ≤ 6) ∧
    (∀ n : ℕ, 0 < n →
      coordinateHolderENorm 2 alpha.value Set.univ (liftedOscillation alpha.value n) ≤
        ENNReal.ofReal (5 / (n : ℝ))) ∧
    Tendsto (fun n : ℕ =>
      (coordinateHolderENorm 2 alpha.value Set.univ (liftedOscillation alpha.value n)).toReal)
      atTop (𝓝 0) ∧
    (∀ n : ℕ, 2 ≤ n →
      let D := fun r : ℝ =>
        expectedDefectCoefficients alpha.value n (r • basisVector 0) 0
      let Q := |deriv D 0 - deriv D (Real.pi / n)| /
        Real.rpow |(0 : ℝ) - Real.pi / n| (alpha.value : ℝ)
      Q = (1 + 2 / (n : ℝ)^2) * Real.rpow Real.pi (-(alpha.value : ℝ)) ∧
      Real.rpow Real.pi (-(alpha.value : ℝ)) ≤ Q) ∧
    ¬ (∃ K : ℝ, ∀ n : ℕ, 2 ≤ n →
      let D := fun r : ℝ =>
        expectedDefectCoefficients alpha.value n (r • basisVector 0) 0
      |deriv D 0 - deriv D (Real.pi / n)| /
        Real.rpow |(0 : ℝ) - Real.pi / n| (alpha.value : ℝ) ≤
      K * (coordinateHolderENorm 2 alpha.value Set.univ
        (liftedOscillation alpha.value n)).toReal) := by
  intro alpha
  have ha : alpha.value ≤ 1 := alpha.lessThanOne.le
  refine ⟨oscillatingScalar_quotientMap alpha.value, ?_,
    fun n hn => scalar_C2alpha_bound alpha.value ha hn,
    scalar_C2alpha_tendsto_zero alpha.value ha, ?_, ?_⟩
  · intro n
    have hs := liftedOscillation_smooth (alpha.value : ℝ) n
    have hb := scalar_C3alpha_bound_all alpha.value ha n
    exact ⟨hs,
      ⟨(contDiff_infty.mp hs 2).contDiffOn,
        scalar_C2alpha_finite alpha.value ha n⟩,
      ⟨(contDiff_infty.mp hs 3).contDiffOn,
        hb.trans_lt (by norm_num)⟩, hb⟩
  · intro n hn
    change defectHolderWitness alpha.value n = _ ∧ _ ≤ defectHolderWitness alpha.value n
    exact ⟨defectHolderWitness_eq alpha.value (by omega),
      defectHolderWitness_lower alpha.value (by omega)⟩
  · exact no_scalar_shifted_bound alpha.value ha
