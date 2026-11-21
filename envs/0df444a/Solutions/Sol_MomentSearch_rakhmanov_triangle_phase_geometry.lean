-- Prove2me | solution 1 for MomentSearch.rakhmanov_triangle_phase_geometry
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T00:21:44.932558+00:00
-- url     : https://prove2.me/submissions/8faaa8d6-f6b5-40dc-9a7a-18b4ba49c613

import Mathlib

open Complex

/-- The principal complex arctangent is differentiable on the open right half-plane. -/
theorem hasDerivAt_complexArctan_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    HasDerivAt Complex.arctan (1 / (1 + z ^ 2)) z := by
  let a (u : ℂ) := 1 + u * Complex.I
  let b (u : ℂ) := 1 - u * Complex.I
  have ha : a z ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp [a, Complex.mul_im] at hi
    linarith
  have hb : b z ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp [b, Complex.mul_im] at hi
    linarith
  have hs : a z / b z ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    apply ne_of_gt
    rw [Complex.div_im, ← sub_div]
    have hden : 0 < Complex.normSq (b z) := Complex.normSq_pos.mpr hb
    apply div_pos _ hden
    simp [a, b, Complex.mul_im, Complex.mul_re]
    nlinarith
  have h1 : HasDerivAt a Complex.I z := by
    simpa only [one_mul] using ((hasDerivAt_id' z).mul_const Complex.I).const_add 1
  have h2 : HasDerivAt b (-Complex.I) z := by
    simpa only [one_mul] using ((hasDerivAt_id' z).mul_const Complex.I).const_sub 1
  have hder := ((h1.div h2 hb).clog hs).const_mul (-Complex.I / 2)
  have hprod : (1 : ℂ) + z ^ 2 = a z * b z := by
    dsimp [a,b]
    calc
      _ = 1 - z ^ 2 * Complex.I ^ 2 := by rw [Complex.I_sq]; ring
      _ = _ := by ring
  have he :
      (-Complex.I / 2) * (((Complex.I * b z - a z * -Complex.I) / b z ^ 2) / (a z / b z)) =
        1 / (1 + z ^ 2) := by
    rw [hprod]
    have hab : a z + b z = 2 := by dsimp [a,b]; ring
    have hsum : Complex.I * b z - a z * -Complex.I = 2 * Complex.I := by
      linear_combination Complex.I * hab
    rw [hsum]
    field_simp [ha, hb]
    norm_num [Complex.I_sq]
  change HasDerivAt Complex.arctan
    ((-Complex.I / 2) * (((Complex.I * b z - a z * -Complex.I) / b z ^ 2) / (a z / b z))) z at hder
  rwa [he] at hder

open Set MeasureTheory
open scoped Real

private theorem arctan_continuousAt_zero : ContinuousAt Complex.arctan 0 := by
  have hA : ContinuousAt (fun z : ℂ => (1 + z * Complex.I) / (1 - z * Complex.I)) 0 :=
    (by fun_prop : Continuous fun z : ℂ => 1 + z * Complex.I).continuousAt.div
      (by fun_prop : Continuous fun z : ℂ => 1 - z * Complex.I).continuousAt (by simp)
  have hL : (1 + 0 * Complex.I) / (1 - 0 * Complex.I) ∈ Complex.slitPlane := by
    simp [Complex.mem_slitPlane_iff]
  exact continuousAt_const.mul ((continuousAt_clog hL).comp (f := fun z : ℂ => (1 + z * Complex.I) / (1 - z * Complex.I)) hA)

private theorem arctan_sector {z : ℂ} (hz : 0 < z.re) (hi : z.im ≤ 0)
    (ha : Real.sqrt 3 * |z.im| ≤ z.re) :
    0 ≤ (Complex.arctan z).re ∧ (Complex.arctan z).im ≤ 0 ∧
      Real.sqrt 3 * |(Complex.arctan z).im| ≤ (Complex.arctan z).re := by
  let s := Real.sqrt (3 : ℝ)
  have hs : 0 < s := by dsimp [s]; positivity
  have hs1 : 1 ≤ s := by dsimp [s]; norm_num
  have hzI : |z.im| ≤ z.re := by
    apply le_trans _ ha
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs1 (abs_nonneg z.im)
  have hsq : z.im ^ 2 ≤ z.re ^ 2 := by
    rw [← sq_abs z.im]
    exact (sq_le_sq₀ (abs_nonneg _) hz.le).mpr hzI
  let P (t : ℝ) : ℂ := 1 + ((t : ℂ) * z)^2
  have hPre (t : ℝ) : 0 < (P t).re := by
    simp only [P, pow_two, Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.mul_im]
    nlinarith only [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hsq)]
  have hP (t : ℝ) : P t ≠ 0 := by
    intro he
    simpa [he] using hPre t
  let F (t : ℝ) : ℂ := z / P t
  have hFc : Continuous F :=
    continuous_const.div (by unfold P; fun_prop) hP
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => Complex.arctan ((t : ℂ) * z)) (F t) t := by
    have hpos : 0 < ((t : ℂ) * z).re := by simpa using mul_pos ht.1 hz
    have hlinear : HasDerivAt (fun t : ℂ => t * z) z (t : ℂ) := by
      simpa only [one_mul] using (hasDerivAt_id' (t : ℂ)).mul_const z
    have h := ((hasDerivAt_complexArctan_of_re_pos _ hpos).comp (t : ℂ) hlinear).comp_ofReal
    simpa only [F, P, div_mul_eq_mul_div, one_mul, Function.comp_apply] using h
  have hArctan (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContinuousAt (fun t : ℝ => Complex.arctan ((t : ℂ) * z)) t := by
    rcases ht.1.eq_or_lt with he | he
    · subst t
      have hL : ContinuousAt (fun t : ℝ => (t : ℂ) * z) (0 : ℝ) :=
        (by fun_prop : Continuous (fun t : ℝ => (t : ℂ) * z)).continuousAt
      have hAt : ContinuousAt Complex.arctan ((0:ℂ)*z) := by simpa using arctan_continuousAt_zero
      exact hAt.comp (f := fun t : ℝ => (t : ℂ)*z) hL
    · have hpos : 0 < ((t : ℂ) * z).re := by simpa using mul_pos he hz
      exact (hasDerivAt_complexArctan_of_re_pos _ hpos).continuousAt.comp (f := fun t : ℝ => (t : ℂ)*z)
        (by fun_prop : ContinuousAt (fun t : ℝ => (t : ℂ) * z) t)
  have hFcInt := hFc.intervalIntegrable (μ := volume) 0 1
  have hI : (∫ t in (0 : ℝ)..1, F t) = Complex.arctan z := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num)
      (fun t ht => (hArctan t ht).continuousWithinAt) hd hFcInt]
    simp [Complex.arctan]
  have hF_re (t : ℝ) :
      (F t).re = z.re * (1 + t^2 * Complex.normSq z) / Complex.normSq (P t) := by
    change (z / P t).re = _
    rw [Complex.div_re, ← add_div]
    congr 1
    simp only [P, pow_two, Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.mul_im, zero_add,
      Complex.add_im, Complex.one_im, Complex.normSq_apply]
    ring
  have hF_im (t : ℝ) :
      (F t).im = z.im * (1 - t^2 * Complex.normSq z) / Complex.normSq (P t) := by
    change (z / P t).im = _
    rw [Complex.div_im, ← sub_div]
    congr 1
    simp only [P, pow_two, Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.mul_im, zero_add,
      Complex.add_im, Complex.one_im, Complex.normSq_apply]
    ring
  have hFre (t : ℝ) : 0 ≤ (F t).re := by
    rw [hF_re]
    exact div_nonneg (mul_nonneg hz.le (by linarith [mul_nonneg (sq_nonneg t) (Complex.normSq_nonneg z)])) (Complex.normSq_nonneg _)
  have hFabs (t : ℝ) : s * |(F t).im| ≤ (F t).re := by
    rw [hF_re, hF_im, abs_div, abs_mul, abs_of_nonneg (Complex.normSq_nonneg _), ← mul_div_assoc,
      ← mul_assoc]
    have hq : 0 ≤ t^2 * Complex.normSq z := mul_nonneg (sq_nonneg t) (Complex.normSq_nonneg z)
    exact div_le_div_of_nonneg_right
      (mul_le_mul ha (abs_le.mpr ⟨by linarith, by linarith⟩)
        (abs_nonneg _) hz.le) (Complex.normSq_nonneg _)
  have hre := intervalIntegral.intervalIntegral_re hFcInt
  have him := intervalIntegral.intervalIntegral_im hFcInt
  change (∫ t in (0:ℝ)..1, (F t).re) = (∫ t in (0:ℝ)..1, F t).re at hre
  change (∫ t in (0:ℝ)..1, (F t).im) = (∫ t in (0:ℝ)..1, F t).im at him
  rw [hI] at hre him
  have hFcIm := (Complex.continuous_im.comp hFc).intervalIntegrable (μ := volume) 0 1
  have hFcRe := (Complex.continuous_re.comp hFc).intervalIntegrable (μ := volume) 0 1
  have hsector : s * |(Complex.arctan z).im| ≤ (Complex.arctan z).re := by
    rw [← him, ← hre]
    calc
      _ ≤ s * ∫ t in (0:ℝ)..1, |(F t).im| := by
        apply mul_le_mul_of_nonneg_left _ hs.le
        exact intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ ≤ _ := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_mono_on (by norm_num) (hFcIm.abs.const_mul _) hFcRe
          (fun t _ => hFabs t)
  refine ⟨(mul_nonneg hs.le (abs_nonneg _)).trans hsector, ?_, hsector⟩
  have hb : (1 - z * Complex.I) ≠ 0 := by
    intro h
    have e := congrArg Complex.im h
    simp [Complex.mul_im] at e
    linarith
  have hab : ‖1 - z * Complex.I‖ ≤ ‖1 + z * Complex.I‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
      Complex.sub_re, Complex.mul_re, Complex.one_re, Complex.I_re, Complex.I_im,
      Complex.mul_im, Complex.add_im, Complex.sub_im, Complex.one_im,
      mul_zero, mul_one, zero_add, add_zero]
    nlinarith only [hi]
  have hl : 0 ≤ Real.log ‖(1 + z * Complex.I) / (1 - z * Complex.I)‖ := by
    apply Real.log_nonneg
    rw [norm_div, le_div_iff₀ (norm_pos_iff.mpr hb), one_mul]
    exact hab
  unfold Complex.arctan
  rw [Complex.mul_im, Complex.log_re]
  norm_num [Complex.div_ofReal_re, Complex.div_ofReal_im] at *
  linarith

open Complex Set
open scoped Real

private noncomputable def triangleStep : ℂ := ⟨1/2, -Real.sqrt 3 / 2⟩
private noncomputable def triangleStepRoot : ℂ := ⟨Real.sqrt 3 / 2, -1/2⟩
private noncomputable def triangleSquare (t : ℝ) : ℂ :=
  (t : ℂ) * triangleStep * (2 - triangleStep * (t : ℂ))

private theorem sqrt_three_sq : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)

private theorem half_power_sq (z : ℂ) : (z ^ (1/2 : ℂ)) ^ (2 : ℕ) = z := by
  rw [← Complex.cpow_mul_nat]
  norm_num

private theorem half_power_pos_re {z : ℂ} (hz : 0 < z.re) :
    0 < (z ^ (1/2 : ℂ)).re := by
  have hne : z ≠ 0 := by intro he; rw [he] at hz; norm_num at hz
  have ha := abs_lt.mp ((Complex.abs_arg_lt_pi_div_two_iff).mpr (Or.inl hz))
  rw [Complex.cpow_def_of_ne_zero hne, Complex.exp_re]
  apply mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo _)
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num [Complex.ofReal_div]
  rw [hhalf, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.log_im, mul_zero, zero_add]
  exact ⟨by linarith [ha.1, Real.pi_pos], by linarith [ha.2, Real.pi_pos]⟩

private theorem complex_two_re : (2 : ℂ).re = 2 := by norm_num
private theorem complex_two_im : (2 : ℂ).im = 0 := by norm_num

private theorem triangle_coords (t : ℝ) :
    (triangleSquare t).re = t * (1 + t/2) ∧
      (triangleSquare t).im = -Real.sqrt 3 * t * (1 - t/2) := by
  constructor
  · simp only [triangleSquare, triangleStep, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, Complex.sub_im, complex_two_re, complex_two_im,
      Complex.ofReal_im, zero_mul, mul_zero, add_zero, zero_add, sub_zero, zero_sub]
    nlinarith only [congrArg (fun u : ℝ => u * t^2) sqrt_three_sq]
  · simp only [triangleSquare, triangleStep, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, Complex.sub_im, complex_two_re, complex_two_im,
      zero_mul, mul_zero, add_zero, zero_add, sub_zero, zero_sub]
    ring

private theorem triangle_roots (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 2) :
    let S := triangleSquare t
    let W := S ^ (1/2 : ℂ)
    let V := (2 - triangleStep * (t : ℂ)) ^ (1/2 : ℂ)
    0 < W.re ∧ W.im ≤ 0 ∧ Real.sqrt 3 * |W.im| ≤ W.re ∧
      0 < V.re ∧ 0 ≤ V.im ∧ W = (Real.sqrt t : ℂ) * triangleStepRoot * V := by
  intro S W V
  have hS := triangle_coords t
  have hSr : 0 < S.re := by
    exact hS.1 ▸ mul_pos ht.1 (by linarith [ht.1])
  have hSi : S.im ≤ 0 := by
    rw [show S.im = _ from hS.2]
    have hs : 0 ≤ Real.sqrt (3:ℝ) := Real.sqrt_nonneg _
    nlinarith only [mul_nonneg (mul_nonneg hs ht.1.le) (show 0 ≤ 1-t/2 by linarith [ht.2])]
  have hW2 : W^2 = S := half_power_sq _
  have hWr : 0 < W.re := half_power_pos_re hSr
  have hWre : W.re^2 - W.im^2 = S.re := by
    have h := congrArg Complex.re hW2
    simpa only [pow_two, Complex.mul_re] using h
  have hWim : 2 * W.re * W.im = S.im := by
    have h := congrArg Complex.im hW2
    simp only [pow_two, Complex.mul_im] at h
    linarith only [h]
  have hWi : W.im ≤ 0 :=
    nonpos_of_mul_nonpos_right (a := 2 * W.re) (b := W.im)
      (by rw [hWim]; exact hSi) (by positivity)
  have hWt : Real.sqrt 3 * |W.im| ≤ W.re := by
    have hs : 0 < Real.sqrt (3:ℝ) := Real.sqrt_pos.mpr (by norm_num)
    have hSangle : -S.im ≤ Real.sqrt 3 * S.re := by
      change -(triangleSquare t).im ≤ Real.sqrt 3 * (triangleSquare t).re
      rw [hS.1, hS.2]
      nlinarith only [mul_nonneg hs.le (sq_nonneg t)]
    rw [← hWre, ← hWim] at hSangle
    rw [abs_of_nonpos hWi]
    have hfac : 0 ≤ (W.re - Real.sqrt 3 * (-W.im)) * (Real.sqrt 3 * W.re - W.im) := by
      nlinarith only [hSangle, congrArg (fun u : ℝ => u * W.re * W.im) sqrt_three_sq]
    exact sub_nonneg.mp
      (nonneg_of_mul_nonneg_left hfac (by nlinarith [mul_pos hs hWr]))
  have hV0 : (0 : ℝ) < (2 - triangleStep * (t : ℂ)).re := by
    simp only [triangleStep, Complex.sub_re, Complex.mul_re, complex_two_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    linarith [ht.2]
  have hVr : 0 < V.re := half_power_pos_re hV0
  have hV2 : V ^ 2 = 2 - triangleStep * (t : ℂ) := half_power_sq _
  have hVi : 0 ≤ V.im := by
    have he := congrArg Complex.im hV2
    simp only [triangleStep, pow_two, Complex.mul_im, Complex.sub_im, complex_two_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, zero_sub] at he
    apply nonneg_of_mul_nonneg_right (a := (2 * V.re))
    · nlinarith only [he, mul_nonneg (Real.sqrt_nonneg 3) ht.1.le]
    · positivity
  refine ⟨hWr, hWi, hWt, hVr, hVi, ?_⟩
  let U := (Real.sqrt t : ℂ) * triangleStepRoot * V
  have hUr : 0 < U.re := by
    dsimp only [U, triangleStepRoot]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    have ht0 := Real.sqrt_pos.mpr ht.1
    have h3 := Real.sqrt_pos.mpr (show (0:ℝ)<3 by norm_num)
    have hA := mul_pos (mul_pos ht0 (div_pos h3 (by norm_num : (0:ℝ) < 2))) hVr
    have hB := mul_nonneg (mul_nonneg ht0.le (show 0 ≤ (1/2:ℝ) by norm_num)) hVi
    nlinarith only [hA, hB]
  have hR2 : triangleStepRoot ^ (2 : ℕ) = triangleStep := by
    apply Complex.ext
    · simp only [triangleStepRoot, triangleStep, pow_two, Complex.mul_re]
      nlinarith only [sqrt_three_sq]
    · simp only [triangleStepRoot, triangleStep, pow_two, Complex.mul_im]
      ring
  have hU2 : U ^ 2 = S := by
    dsimp only [U, S, triangleSquare]
    rw [mul_pow, mul_pow, hR2, hV2, ← Complex.ofReal_pow, Real.sq_sqrt ht.1.le]
  change S ^ (1/2 : ℂ) = U
  rw [← hU2, show (1 / 2 : ℂ) = 2⁻¹ by ring]
  exact Complex.sq_cpow_two_inv hUr

private theorem triangle_kernel_re_nonneg (t c : ℝ) (ht : t ∈ Ioc (0 : ℝ) 2) (hc : 0 ≤ c) :
    let S := triangleSquare t
    let V := (2 - triangleStep * (t : ℂ)) ^ (1/2 : ℂ)
    0 ≤ ((1 - triangleStep * (t : ℂ)) / (V * (1 + (c : ℂ) * S))).re := by
  intro S V
  let h := t/2
  let s := Real.sqrt (3 : ℝ)
  let U : ℂ := 1 - triangleStep * (t : ℂ)
  let P : ℂ := 2 - triangleStep * (t : ℂ)
  have hh : 0 ≤ h := div_nonneg ht.1.le (by norm_num)
  have hh1 : h ≤ 1 := by dsimp [h]; linarith [ht.2]
  have hs : 0 < s := by dsimp [s]; positivity
  have hs2 : s^2 = 3 := sqrt_three_sq
  obtain ⟨_, _, _, hVr, hVi, _⟩ := triangle_roots t ht
  change 0 < V.re at hVr
  change 0 ≤ V.im at hVi
  have hPre : P.re = 2-h := by
    simp [P, h, triangleStep, Complex.mul_re]
    ring
  have hPim : P.im = s*h := by
    simp [P, h, s, triangleStep, Complex.mul_im]
    ring
  have hUre : U.re = 1-h := by
    simp [U, h, triangleStep, Complex.mul_re]
    ring
  have hUim : U.im = s*h := by
    simp [U, h, s, triangleStep, Complex.mul_im]
    ring
  have hSre : S.re = t*(1+h) := (triangle_coords t).1
  have hSim : S.im = -s*t*(1-h) := (triangle_coords t).2
  have hV2 : V^2 = P := half_power_sq P
  have hVre : V.re^2 - V.im^2 = 2-h := by
    have he := congrArg Complex.re hV2
    simpa only [pow_two, Complex.mul_re, hPre] using he
  have hVim : 2 * V.re * V.im = s*h := by
    have he := congrArg Complex.im hV2
    simp only [pow_two, Complex.mul_im, hPim] at he
    linarith only [he]
  have hPn : ‖P‖ ≤ 2 := by
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤2)).mp
    rw [Complex.sq_norm, Complex.normSq_apply, hPre, hPim]
    nlinarith only [mul_nonneg hh (sub_nonneg.mpr hh1),
      congrArg (fun u : ℝ => u*h^2) hs2]
  have hVnorm : V.re^2 + V.im^2 = ‖P‖ := by
    rw [← hV2, norm_pow, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hVr2 : V.re ^ 2 ≤ 2 := by linarith only [hPn, hVnorm, hVre, hh]
  have hlow : s * h * V.re ≤ 4 * V.im := by
    nlinarith only [mul_le_mul_of_nonneg_right hVr2 hVi,
      congrArg (fun x : ℝ => x * V.re) hVim]
  have hfirst : 0 ≤ (U * (starRingEnd ℂ) V).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, hUre, hUim]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hh1) hVr.le,
      mul_nonneg (mul_nonneg hs.le hh) hVi]
  have hUSre : (U * (starRingEnd ℂ) S).re = t * ((1-h)*(1-2*h)) := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, hUre, hUim, hSre, hSim]
    linear_combination -(h*t*(1-h)) * hs2
  have hUSim : (U * (starRingEnd ℂ) S).im = t * (s*(1-h+2*h^2)) := by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, hUre, hUim, hSre, hSim]
    ring
  have hpolypos : 0 ≤ 1-h+2*h^2 := by nlinarith only [hh1, sq_nonneg h]
  have hsecond : 0 ≤ (U * (starRingEnd ℂ) S * (starRingEnd ℂ) V).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, hUSre]
    rw [hUSim]
    have he : t * ((1-h)*(1-2*h)) * V.re - t * (s*(1-h+2*h^2)) * -V.im =
        t * (((1-h)*(1-2*h))*V.re + (s*(1-h+2*h^2))*V.im) := by ring
    rw [he]
    apply mul_nonneg ht.1.le
    by_cases hhmid : h ≤ 1/2
    · exact add_nonneg
        (mul_nonneg (mul_nonneg (sub_nonneg.mpr hh1) (by linarith)) hVr.le)
        (mul_nonneg (mul_nonneg hs.le hpolypos) hVi)
    · have hmid : 0 ≤ h - 1/2 := by linarith
      have hpoly : 4*(1-h)*(2*h-1) ≤ 3*h*(1-h+2*h^2) := by
        apply sub_nonneg.mp
        calc
          _ = 3/2 + (h-1/2)/2 + 14*(h-1/2)^2 + 6*(h-1/2)^3 := by ring
          _ ≥ 0 := by positivity
      have hlow' := mul_le_mul_of_nonneg_left hlow (mul_nonneg hs.le hpolypos)
      have hpoly' := mul_le_mul_of_nonneg_right hpoly hVr.le
      nlinarith only [hlow', hpoly', congrArg (fun u : ℝ => u*h*(1-h+2*h^2)*V.re) hs2]
  let den : ℂ := V * (1 + (c : ℂ) * S)
  have hstar : U * (starRingEnd ℂ) den =
      U * (starRingEnd ℂ) V + (c : ℂ) * (U * (starRingEnd ℂ) S * (starRingEnd ℂ) V) := by
    simp only [den, map_add, map_mul, map_one, Complex.conj_ofReal]
    ring
  have hn : 0 ≤ (U * (starRingEnd ℂ) den).re := by
    rw [hstar, Complex.add_re, Complex.mul_re (c:ℂ)]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact add_nonneg hfirst (mul_nonneg hc hsecond)
  change 0 ≤ (U / den).re
  rw [Complex.div_re, ← add_div]
  apply div_nonneg _ (Complex.normSq_nonneg _)
  simpa only [Complex.mul_re, Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add] using hn

private theorem complex_deriv_re {f : ℝ → ℂ} {a : ℂ} {x : ℝ}
    (hf : HasDerivAt f a x) : HasDerivAt (fun y => (f y).re) a.re x := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hf

private noncomputable def triangleZ (r : ℝ) (t : ℂ) : ℂ :=
  (r : ℂ) * (1 - triangleStep * t)

private noncomputable def triangleD (r : ℝ) (t : ℂ) : ℂ :=
  (r : ℂ)^2 - (triangleZ r t)^2

private noncomputable def triangleW (r : ℝ) (t : ℂ) : ℂ :=
  triangleD r t ^ (1/2 : ℂ)

private noncomputable def triangleAmp (N r a : ℝ) (t : ℂ) : ℂ :=
  2 * Complex.I * (N : ℂ) * (r : ℂ) * triangleStep *
    Complex.arctan ((a : ℂ) * triangleW r t)

private theorem triangleD_eq (r t : ℝ) :
    triangleD r (t : ℂ) = (r : ℂ)^2 * triangleSquare t := by
  unfold triangleD triangleZ triangleSquare
  ring

private theorem triangleW_scaled (r t : ℝ) (hr : 0 < r) (ht : t ∈ Ioc (0 : ℝ) 2) :
    triangleW r (t : ℂ) = (r : ℂ) * (triangleSquare t ^ (1/2 : ℂ)) := by
  obtain ⟨hW, _, _, _, _, _⟩ := triangle_roots t ht
  have hp : 0 < (((r:ℂ) * (triangleSquare t ^ (1 / 2:ℂ)))).re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos hr hW
  have he : (((r : ℂ) * (triangleSquare t ^ (1/2:ℂ))) ^ (2:ℕ)) =
      triangleD r (t : ℂ) := by rw [mul_pow, half_power_sq, triangleD_eq]
  unfold triangleW
  rw [← he]
  simpa only [one_div] using Complex.sq_cpow_two_inv hp

private theorem triangleAmp_cont_at (N r a : ℝ) (hr : 0 < r) (ha : 0 < a)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) :
    ContinuousAt (fun u : ℝ => triangleAmp N r a (u : ℂ)) t := by
  have hDt : 0 ≤ (triangleD r (t : ℂ)).re := by
    rw [triangleD_eq, ← Complex.ofReal_pow, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, (triangle_coords t).1]
    exact mul_nonneg (sq_nonneg _) (mul_nonneg ht.1 (by linarith [ht.1]))
  have hpow : ContinuousAt (fun z : ℂ => z ^ (1 / 2 : ℂ)) (triangleD r (t : ℂ)) :=
    Complex.continuousAt_cpow_const_of_re_pos (Or.inl hDt) (by norm_num [Complex.div_re, complex_two_re, complex_two_im, Complex.normSq_apply])
  have hd : ContinuousAt (fun u : ℝ => triangleD r (u : ℂ)) t := by
    unfold triangleD triangleZ
    fun_prop
  have hW : ContinuousAt (fun u : ℝ => triangleW r (u : ℂ)) t := hpow.comp
    (f := fun u : ℝ => triangleD r (u : ℂ)) hd
  have hA : ContinuousAt (fun u : ℝ => (a : ℂ) * triangleW r (u : ℂ)) t :=
    continuousAt_const.mul hW
  have htA : ContinuousAt Complex.arctan ((a : ℂ) * triangleW r (t : ℂ)) := by
    rcases ht.1.eq_or_lt with he | hp
    · subst t
      have hzero : triangleW r (0 : ℂ) = 0 := by
        rw [← Complex.ofReal_zero]
        unfold triangleW
        rw [triangleD_eq]
        simp [triangleSquare]
      rw [Complex.ofReal_zero, hzero, mul_zero]
      exact arctan_continuousAt_zero
    · have hsc := triangleW_scaled r t hr ⟨hp, ht.2⟩
      obtain ⟨hpos, _, _, _, _, _⟩ := triangle_roots t ⟨hp, ht.2⟩
      have h : 0 < ((a : ℂ) * triangleW r (t : ℂ)).re := by
        rw [hsc, ← mul_assoc, ← Complex.ofReal_mul, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        exact mul_pos (mul_pos ha hr) hpos
      exact (hasDerivAt_complexArctan_of_re_pos _ h).continuousAt
  exact continuousAt_const.mul (htA.comp (f := fun u : ℝ => (a : ℂ) * triangleW r (u : ℂ)) hA)

private theorem triangleAmp_sector (N r a : ℝ) (hN : 0 < N) (hr : 0 < r) (ha : 0 < a)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) :
    0 ≤ (triangleAmp N r a (t : ℂ)).im ∧
      Real.sqrt 3 * (triangleAmp N r a (t : ℂ)).im ≤ (triangleAmp N r a (t : ℂ)).re := by
  rcases ht.1.eq_or_lt with he | hp
  · subst t
    rw [triangleAmp, triangleW, triangleD, triangleZ]
    simp [Complex.arctan]
  let S := triangleSquare t
  let w := S ^ (1/2 : ℂ)
  let z := ((a*r : ℝ) : ℂ) * w
  let q := Complex.arctan z
  obtain ⟨hwr, hwi, hwsect, _, _, _⟩ := triangle_roots t ⟨hp, ht.2⟩
  change 0 < w.re at hwr
  change w.im ≤ 0 at hwi
  change Real.sqrt 3 * |w.im| ≤ w.re at hwsect
  have hzre : z.re = (a*r)*w.re := by
    simp [z, Complex.mul_re]
  have hzim : z.im = (a*r)*w.im := by
    simp [z, Complex.mul_im]
  have hzr : 0 < z.re := by rw [hzre]; positivity
  have hzi : z.im ≤ 0 := by rw [hzim]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hwi
  have hzsec : Real.sqrt 3 * |z.im| ≤ z.re := by
    rw [hzim, hzre, abs_mul, abs_of_nonneg (show 0 ≤ a*r by positivity)]
    simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left hwsect (show 0 ≤ a*r by positivity)
  obtain ⟨hqre, hqim, hqsect⟩ := arctan_sector hzr hzi hzsec
  change 0 ≤ q.re at hqre
  change q.im ≤ 0 at hqim
  change Real.sqrt 3 * |q.im| ≤ q.re at hqsect
  rw [abs_of_nonpos hqim] at hqsect
  have hEq : triangleAmp N r a (t : ℂ) =
      ((N*r : ℝ):ℂ) * (⟨Real.sqrt 3, 1⟩ : ℂ) * q := by
    unfold triangleAmp
    rw [triangleW_scaled r t hr ⟨hp, ht.2⟩]
    have hz : (a : ℂ) * ((r : ℂ) * (triangleSquare t ^ (1/2 : ℂ))) = z := by
      simp only [z, w, S, Complex.ofReal_mul, mul_assoc]
    rw [hz]
    have hs : 2 * Complex.I * triangleStep = (⟨Real.sqrt 3, 1⟩ : ℂ) := by
      apply Complex.ext
      · norm_num [triangleStep, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
        ring
      · norm_num [triangleStep, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [← hs]
    unfold q
    push_cast
    ring
  rw [hEq]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re,
    zero_mul, sub_zero, mul_one]
  constructor
  · nlinarith only [mul_nonneg (mul_nonneg hN.le hr.le) (show 0 ≤ q.re+Real.sqrt 3*q.im by linarith)]
  · nlinarith only [mul_nonneg (mul_nonneg hN.le hr.le) (neg_nonneg.mpr hqim),
      congrArg (fun x : ℝ => x*(N*r)*q.im) sqrt_three_sq]

private theorem triangleAmp_re_deriv (N r a : ℝ) (hN : 0 < N) (hr : 0 < r) (ha : 0 < a)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 2) :
    ∃ c : ℝ, 0 ≤ c ∧ HasDerivAt (fun u : ℝ => (triangleAmp N r a (u : ℂ)).re) c t := by
  let U : ℂ := 1 - triangleStep * (t : ℂ)
  let S := triangleSquare t
  let V := (2 - triangleStep * (t : ℂ)) ^ (1/2 : ℂ)
  let v := Real.sqrt t
  let T := 1 + (((a*r)^2 : ℝ) : ℂ) * S
  let K := 2 * N * r * (a*r) / v
  let W := triangleW r (t : ℂ)
  have ht' : t ∈ Ioc (0 : ℝ) 2 := ⟨ht.1, ht.2.le⟩
  obtain ⟨hwre, _, _, hVre, _, hwfactor⟩ := triangle_roots t ht'
  change (S ^ (1/2:ℂ)) = (v : ℂ) * triangleStepRoot * V at hwfactor
  change 0 < V.re at hVre
  have hfac : W = (r : ℂ) * ((v : ℂ) * triangleStepRoot * V) :=
    (triangleW_scaled r t hr ht').trans (congrArg ((r : ℂ) * ·) hwfactor)
  have hWre : 0 < W.re := by
    change 0 < (triangleW r (t : ℂ)).re
    rw [triangleW_scaled r t hr ht', Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos hr hwre
  have hWne : W ≠ 0 := by intro e; rw [e, Complex.zero_re] at hWre; exact (lt_irrefl _ hWre)
  have hDre : 0 < (triangleD r (t : ℂ)).re := by
    rw [triangleD_eq, ← Complex.ofReal_pow, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, (triangle_coords t).1]
    exact mul_pos (sq_pos_of_pos hr) (mul_pos ht.1 (by linarith [ht.1]))
  have hTne : T ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp only [T, S, Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, (triangle_coords t).1, Complex.zero_re] at hh
    have hP := mul_nonneg (sq_nonneg (a*r)) (mul_nonneg ht.1.le (by linarith [ht.1] : 0 ≤ 1+t/2))
    linarith
  have hVne : V ≠ 0 := by intro e; rw [e, Complex.zero_re] at hVre; exact (lt_irrefl _ hVre)
  have hrootne : triangleStepRoot ≠ 0 := by
    intro e
    have he := congrArg Complex.im e
    norm_num [triangleStepRoot] at he
  have hv : 0 < v := Real.sqrt_pos.mpr ht.1
  have hsq : (1:ℂ) + ((a:ℂ)*W)^2 = T := by
    have hW2 : W^2 = (r:ℂ)^2 * S := (half_power_sq _).trans (triangleD_eq r t)
    rw [mul_pow, hW2]
    simp only [T, Complex.ofReal_pow, Complex.ofReal_mul, mul_pow, mul_assoc]
  have hZ : HasDerivAt (triangleZ r) (-(r:ℂ) * triangleStep) (t:ℂ) := by
    have h_id : HasDerivAt (fun z : ℂ => z) 1 (t:ℂ) := hasDerivAt_id' _
    unfold triangleZ
    convert ((h_id.const_mul triangleStep).const_sub 1).const_mul (r:ℂ) using 1 <;> first | rfl | ring
  have hD : HasDerivAt (triangleD r) (2 * (r:ℂ) * triangleStep * triangleZ r (t:ℂ)) (t:ℂ) := by
    unfold triangleD
    convert (hZ.pow 2).const_sub ((r:ℂ)^2) using 1 <;> first | rfl | ring
  have hW : HasDerivAt (triangleW r) ((r:ℂ)*triangleStep*triangleZ r (t:ℂ) / W) (t:ℂ) := by
    have h := hD.cpow_const (c := (1/2:ℂ)) (Complex.mem_slitPlane_iff.mpr (Or.inl hDre))
    change HasDerivAt (triangleW r)
      ((1/2:ℂ) * triangleD r (t:ℂ) ^ ((1/2:ℂ)-1) *
        (2*(r:ℂ)*triangleStep*triangleZ r (t:ℂ))) (t:ℂ) at h
    have he : (1/2:ℂ) * triangleD r (t:ℂ) ^ ((1/2:ℂ)-1) *
        (2*(r:ℂ)*triangleStep*triangleZ r (t:ℂ)) =
          (r:ℂ)*triangleStep*triangleZ r (t:ℂ) / W := by
      rw [show (1/2:ℂ)-1 = -(1/2:ℂ) by ring, Complex.cpow_neg]
      change (1/2:ℂ) * W⁻¹ * _ = _
      ring
    rwa [he] at h
  have hz : 0 < ((a:ℂ)*W).re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos ha hWre
  have hG := ((hasDerivAt_complexArctan_of_re_pos _ hz).comp (t:ℂ) (hW.const_mul (a:ℂ))).const_mul
    (2 * Complex.I * (N:ℂ) * (r:ℂ) * triangleStep)
  have hf :
      (2 * Complex.I * (N:ℂ) * (r:ℂ) * triangleStep) *
        (1 / (1 + ((a:ℂ)*W)^2) * ((a:ℂ) * ((r:ℂ)*triangleStep*triangleZ r (t:ℂ) / W))) =
      (K : ℂ) * (U / (V*T)) := by
    rw [hsq, hfac]
    have hstep : Complex.I * triangleStep^2 = triangleStepRoot := by
      apply Complex.ext
      · simp [triangleStep, triangleStepRoot, pow_two, Complex.mul_re, Complex.mul_im]
        ring
      · simp [triangleStep, triangleStepRoot, pow_two, Complex.mul_re, Complex.mul_im]
        nlinarith only [sqrt_three_sq]
    have hEq : triangleZ r (t:ℂ) = (r:ℂ)*U := rfl
    rw [hEq, show (K : ℂ) = 2*(N:ℂ)*(r:ℂ)*((a:ℂ)*(r:ℂ))/(v:ℂ) by
      simp [K, Complex.ofReal_div, Complex.ofReal_mul]]
    field_simp [hr.ne', hv.ne', hrootne, hVne, hTne]
    linear_combination (N:ℂ) * (a:ℂ) * U * hstep
  change HasDerivAt (triangleAmp N r a)
    ((2 * Complex.I * (N:ℂ) * (r:ℂ) * triangleStep) *
        (1 / (1 + ((a:ℂ)*W)^2) * ((a:ℂ) * ((r:ℂ)*triangleStep*triangleZ r (t:ℂ) / W)))) (t:ℂ) at hG
  rw [hf] at hG
  refine ⟨((K:ℂ) * (U/(V*T))).re, ?_, complex_deriv_re hG.comp_ofReal⟩
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (by positivity) (triangle_kernel_re_nonneg t ((a*r)^2) ht' (sq_nonneg _))
open scoped Topology



theorem solution (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let s : ℂ := ⟨1/2, -Real.sqrt 3 / 2⟩
    let Z : ℝ → ℂ := fun t => (r : ℂ) * (1 - s * t)
    let B : ℝ → ℂ := fun t => 2 * Complex.I * (N : ℂ) * r * s *
      ∫ v in (0 : ℝ)..t, Complex.arctan ((N : ℂ) / k *
        (((r : ℂ)^2 - (Z v)^2) ^ (1/2 : ℂ)))
    ∃ d : ℝ → ℝ,
      ContinuousOn B (Set.Icc 0 2) ∧ ContinuousOn d (Set.Icc 0 2) ∧
      (B 0).re = 0 ∧
      (∀ t ∈ Set.Ioo 0 2, HasDerivAt (fun u => (B u).re) (d t) t) ∧
      (∀ t ∈ Set.Ioo 0 2, (B t).re / t ≤ d t) ∧
      ∀ t ∈ Set.Icc 0 2, Real.sqrt 3 * |(B t).im| ≤ (B t).re := by
  intro r s Z B
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hk' : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkN' : (k:ℝ) < N := by exact_mod_cast hkN
  have hr : 0 < r := by
    unfold r
    apply Real.sqrt_pos.mpr
    rw [← div_pow, sub_pos]
    simpa using (sq_lt_sq₀ (div_nonneg hk'.le hN.le) zero_le_one).mpr ((div_lt_one hN).mpr hkN')
  let a : ℝ := (N : ℝ) / k
  have ha : 0 < a := div_pos hN hk'
  let G : ℝ → ℂ := fun t => triangleAmp (N : ℝ) r a (t : ℂ)
  let d : ℝ → ℝ := fun t => (G t).re
  let R : ℝ → ℝ := fun t => (B t).re
  have hB_int (t : ℝ) : B t = ∫ u in (0 : ℝ)..t, G u := by
    unfold B G triangleAmp triangleW triangleD triangleZ a s Z
    push_cast
    rw [intervalIntegral.integral_const_mul]
    rfl
  have hGc (t : ℝ) (ht : t ∈ Icc (0:ℝ) 2) : ContinuousAt G t :=
    triangleAmp_cont_at (N:ℝ) r a hr ha t ht
  have hGcOn : ContinuousOn G (Icc (0:ℝ) 2) := fun t ht => (hGc t ht).continuousWithinAt
  have hGInt (t : ℝ) (ht : t ∈ Icc (0:ℝ) 2) : IntervalIntegrable G volume 0 t := by
    apply ContinuousOn.intervalIntegrable_of_Icc ht.1
    exact hGcOn.mono (Icc_subset_Icc_right ht.2)
  have hBc : ContinuousOn B (Icc (0:ℝ) 2) := by
    have h := intervalIntegral.continuousOn_primitive_interval' (hGInt 2 (by constructor <;> norm_num))
      (left_mem_uIcc (a := (0:ℝ)) (b := 2))
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)] at h
    exact h.congr (fun t _ => hB_int t)
  have hB0 : B 0 = 0 := by rw [hB_int, intervalIntegral.integral_same]
  have hBd (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 2) : HasDerivAt R (d t) t := by
    have ht' : t ∈ Icc (0:ℝ) 2 := Ioo_subset_Icc_self ht
    have hm : StronglyMeasurableAtFilter G (𝓝 t) :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hGcOn.mono Ioo_subset_Icc_self) t ht
    have he := intervalIntegral.integral_hasDerivAt_right (hGInt t ht') hm (hGc t ht')
    have hBder : HasDerivAt B (G t) t :=
      he.congr_of_eventuallyEq (Filter.Eventually.of_forall hB_int)
    exact complex_deriv_re hBder
  have hBdd (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 2) :
      ∃ c, 0 ≤ c ∧ HasDerivAt d c t := triangleAmp_re_deriv (N:ℝ) r a hN hr ha t ht
  classical
  let dd (t : ℝ) := if ht : t ∈ Ioo (0:ℝ) 2 then (hBdd t ht).choose else 0
  have hconvex : ConvexOn ℝ (Icc (0:ℝ) 2) R := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (f' := d) (f'' := dd) (convex_Icc _ _)
    · exact Complex.continuous_re.comp_continuousOn hBc
    · rw [interior_Icc]
      exact fun t ht => (hBd t ht).hasDerivWithinAt
    · rw [interior_Icc]
      intro t ht
      unfold dd
      rw [dif_pos ht]
      exact (hBdd t ht).choose_spec.2.hasDerivWithinAt
    · rw [interior_Icc]
      intro t ht
      unfold dd
      rw [dif_pos ht]
      exact (hBdd t ht).choose_spec.1
  refine ⟨d, hBc, Complex.continuous_re.comp_continuousOn hGcOn, by rw [hB0, Complex.zero_re],
    hBd, ?_, ?_⟩
  · intro t ht
    have h := hconvex.slope_le_of_hasDerivAt (by constructor <;> norm_num : (0:ℝ) ∈ Icc 0 2)
      (Ioo_subset_Icc_self ht) ht.1 (hBd t ht)
    rwa [slope_def_field, show R 0 = 0 by exact congrArg Complex.re hB0, sub_zero, sub_zero] at h
  · intro t ht
    have hI := hGInt t ht
    have hre := intervalIntegral.intervalIntegral_re hI
    have him := intervalIntegral.intervalIntegral_im hI
    change (∫ u in (0:ℝ)..t, (G u).re) = (∫ u in (0:ℝ)..t, G u).re at hre
    change (∫ u in (0:ℝ)..t, (G u).im) = (∫ u in (0:ℝ)..t, G u).im at him
    rw [← hB_int t] at hre him
    have hGsec (u : ℝ) (hu : u ∈ Icc (0:ℝ) t) :
        0 ≤ (G u).im ∧ Real.sqrt 3 * (G u).im ≤ (G u).re :=
      triangleAmp_sector (N:ℝ) r a hN hr ha u (Icc_subset_Icc_right ht.2 hu)
    have hBi : 0 ≤ (B t).im := by
      rw [← him]
      exact intervalIntegral.integral_nonneg ht.1 (fun u hu => (hGsec u hu).1)
    rw [abs_of_nonneg hBi, ← him, ← hre, ← intervalIntegral.integral_const_mul]
    have hsub := hGcOn.mono (Icc_subset_Icc_right ht.2)
    have hIm := (Complex.continuous_im.comp_continuousOn hsub).intervalIntegrable_of_Icc
      (μ := volume) ht.1
    have hRe := (Complex.continuous_re.comp_continuousOn hsub).intervalIntegrable_of_Icc
      (μ := volume) ht.1
    exact intervalIntegral.integral_mono_on ht.1 (hIm.const_mul _) hRe (fun u hu => (hGsec u hu).2)
