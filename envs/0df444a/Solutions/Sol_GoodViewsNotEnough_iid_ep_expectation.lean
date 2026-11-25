-- Prove2me | solution 1 for GoodViewsNotEnough.iid_ep_expectation
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T16:43:03.315216+00:00
-- url     : https://prove2.me/submissions/33bb6e87-d1fe-4450-8ffa-b0514a96a528

import Mathlib
import Definitions.Def_GoodViewsNotEnough_Basic

open MeasureTheory Complex
open scoped ENNReal

namespace GoodViewsNotEnough

lemma ie_nz (t x : ℝ) : ‖Complex.exp (t * x * I)‖ = 1 := by
  have : (t : ℂ) * x * I = ((t * x : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma ie_cf {N : ℕ} (y : Fin N → ℝ) (t : ℝ) :
    charFun (empiricalLaw y) t = (N : ℂ)⁻¹ * ∑ n, Complex.exp (t * y n * I) := by
  rw [charFun_apply_real, empiricalLaw, integral_finsetSum_measure]
  · simp [integral_smul_measure, integral_dirac, Finset.mul_sum]
  · intro n _
    have h0 : Integrable (fun x : ℝ => Complex.exp (t * x * I)) (Measure.dirac (y n)) :=
      Integrable.of_bound ((by fun_prop : Continuous fun x : ℝ =>
        Complex.exp (t * x * I)).aestronglyMeasurable) 1 (ae_of_all _ fun x => (ie_nz t x).le)
    exact h0.smul_measure (ENNReal.inv_ne_top.2 (by simpa using (Fin.pos n).ne'))

lemma ie_int {N : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] (F : (Fin N → ℝ) → ℂ)
    (hF : Continuous F) (C : ℝ) (hC : ∀ y, ‖F y‖ ≤ C) :
    Integrable F (Measure.pi fun _ : Fin N => μ) :=
  Integrable.of_bound hF.aestronglyMeasurable C (ae_of_all _ hC)

lemma ie_E1 {N : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] (z : ℝ → ℂ) (n : Fin N) :
    ∫ y, z (y n) ∂(Measure.pi fun _ : Fin N => μ) = ∫ x, z x ∂μ := by
  have h := integral_fintype_prod_eq_prod (μ := fun _ : Fin N => μ)
    (fun i (x : ℝ) => if i = n then z x else 1)
  have hl : ∀ y : Fin N → ℝ, ∏ i, (if i = n then z (y i) else 1) = z (y n) := fun y => by
    rw [Fintype.prod_eq_single n (fun i hi => by simp [hi])]; simp
  have hr : ∏ i, ∫ x, (if i = n then z x else (1:ℂ)) ∂μ = ∫ x, z x ∂μ := by
    rw [Fintype.prod_eq_single n (fun i hi => by simp [hi])]; simp
  simp only [hl, hr] at h; exact h

lemma ie_E2 {N : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] (z w : ℝ → ℂ) (n m : Fin N)
    (hnm : n ≠ m) :
    ∫ y, z (y n) * w (y m) ∂(Measure.pi fun _ : Fin N => μ) = (∫ x, z x ∂μ) * ∫ x, w x ∂μ := by
  have h := integral_fintype_prod_eq_prod (μ := fun _ : Fin N => μ)
    (fun i (x : ℝ) => if i = n then z x else if i = m then w x else 1)
  have hl : ∀ y : Fin N → ℝ, ∏ i, (if i = n then z (y i) else if i = m then w (y i) else 1)
      = z (y n) * w (y m) := fun y => by
    rw [Fintype.prod_eq_mul n m hnm (fun i hi => by simp [hi.1, hi.2])]; simp [hnm.symm]
  have hr : ∏ i, ∫ x, (if i = n then z x else if i = m then w x else (1:ℂ)) ∂μ
      = (∫ x, z x ∂μ) * ∫ x, w x ∂μ := by
    rw [Fintype.prod_eq_mul n m hnm (fun i hi => by simp [hi.1, hi.2])]; simp [hnm.symm]
  simp only [hl, hr] at h; exact h

lemma ie_sum (N : ℕ) (c : ℂ) :
    ∑ n : Fin N, ∑ m : Fin N, (if n = m then (1:ℂ) else c) = N * (N * c + (1 - c)) := by
  have : ∀ n m : Fin N, (if n = m then (1:ℂ) else c) = c + if n = m then 1 - c else 0 := by
    intro n m; split_ifs <;> ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul]
  ring

lemma ie_pert (N : ℕ) (hN : 0 < N) (μ : Measure ℝ) [IsProbabilityMeasure μ] (t g : ℝ) :
    ∫ y, (N : ℝ) * ‖(N : ℂ)⁻¹ * ∑ n, Complex.exp (t * y n * I) - g‖ ^ 2
        ∂(Measure.pi fun _ : Fin N => μ) =
      N * ‖charFun μ t - g‖ ^ 2 + 1 - ‖charFun μ t‖ ^ 2 := by
  set P := Measure.pi fun _ : Fin N => μ
  obtain ⟨z, hz⟩ : ∃ z : ℝ → ℂ, z = fun x : ℝ => Complex.exp (t * x * I) := ⟨_, rfl⟩
  have hzx : ∀ x : ℝ, Complex.exp (t * x * I) = z x := fun x => by rw [hz]
  simp only [hzx]
  have hzn : ∀ x, ‖z x‖ = 1 := fun x => by rw [← hzx]; exact ie_nz t x
  have hzc : Continuous z := by rw [hz]; fun_prop
  have hφ : charFun μ t = ∫ x, z x ∂μ := by rw [charFun_apply_real]; simp only [hzx]
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have key : ∀ w : ℂ, ((‖w‖ : ℝ) : ℂ) ^ 2 = w * (starRingEnd ℂ) w := by
    intro w; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hpt : ∀ y : Fin N → ℝ,
      (((N : ℝ) * ‖(N : ℂ)⁻¹ * ∑ n, z (y n) - g‖ ^ 2 : ℝ) : ℂ) =
        (N : ℂ)⁻¹ * ∑ n, ∑ m, z (y n) * (starRingEnd ℂ) (z (y m))
          - g * ∑ n, z (y n) - g * ∑ n, (starRingEnd ℂ) (z (y n)) + N * g ^ 2 := by
    intro y
    push_cast
    rw [key]
    simp only [map_sub, map_mul, map_sum, map_inv₀, map_natCast, Complex.conj_ofReal]
    rw [← Finset.sum_mul_sum]
    field_simp
    ring
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, integral_congr_ae (ae_of_all _ hpt)]
  have i1 : ∀ n m : Fin N, Integrable (fun y : Fin N → ℝ =>
      z (y n) * (starRingEnd ℂ) (z (y m))) P := fun n m =>
    ie_int μ _ (by fun_prop) 1 (fun y => by simp [hzn])
  have i2 : ∀ n : Fin N, Integrable (fun y : Fin N → ℝ => z (y n)) P := fun n =>
    ie_int μ _ (by fun_prop) 1 (fun y => by simp [hzn])
  have i3 : ∀ n : Fin N, Integrable (fun y : Fin N → ℝ => (starRingEnd ℂ) (z (y n))) P := fun n =>
    ie_int μ _ (by fun_prop) 1 (fun y => by simp [hzn])
  have ia : Integrable (fun y : Fin N → ℝ =>
      (N : ℂ)⁻¹ * ∑ n, ∑ m, z (y n) * (starRingEnd ℂ) (z (y m))) P :=
    (integrable_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ => i1 n m).const_mul _
  have ib : Integrable (fun y : Fin N → ℝ => (g : ℂ) * ∑ n, z (y n)) P :=
    (integrable_finsetSum _ fun n _ => i2 n).const_mul _
  have ic : Integrable (fun y : Fin N → ℝ => (g : ℂ) * ∑ n, (starRingEnd ℂ) (z (y n))) P :=
    (integrable_finsetSum _ fun n _ => i3 n).const_mul _
  have iab : Integrable (fun y : Fin N → ℝ =>
      (N : ℂ)⁻¹ * ∑ n, ∑ m, z (y n) * (starRingEnd ℂ) (z (y m)) - g * ∑ n, z (y n)) P := ia.sub ib
  have iabc : Integrable (fun y : Fin N → ℝ =>
      (N : ℂ)⁻¹ * ∑ n, ∑ m, z (y n) * (starRingEnd ℂ) (z (y m)) - g * ∑ n, z (y n)
        - g * ∑ n, (starRingEnd ℂ) (z (y n))) P := iab.sub ic
  rw [integral_add iabc (integrable_const _), integral_sub iab ic, integral_sub ia ib,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun n _ => integrable_finsetSum _ fun m _ => i1 n m),
    integral_finsetSum _ (fun n _ => i2 n), integral_finsetSum _ (fun n _ => i3 n)]
  have e2 : ∀ n m : Fin N, ∫ y, z (y n) * (starRingEnd ℂ) (z (y m)) ∂P =
      if n = m then 1 else (charFun μ t) * (starRingEnd ℂ) (charFun μ t) := by
    intro n m
    split_ifs with h
    · subst h
      have : ∀ y : Fin N → ℝ, z (y n) * (starRingEnd ℂ) (z (y n)) = 1 := by
        intro y; rw [← key, hzn]; simp
      simp [this]
    · rw [ie_E2 μ z (fun x => (starRingEnd ℂ) (z x)) n m h, integral_conj, hφ]
  have e2' : ∀ n : Fin N, ∫ a, ∑ m, z (a n) * (starRingEnd ℂ) (z (a m)) ∂P =
      ∑ m, (if n = m then 1 else (charFun μ t) * (starRingEnd ℂ) (charFun μ t)) := fun n => by
    rw [integral_finsetSum _ (fun m _ => i1 n m)]; exact Finset.sum_congr rfl fun m _ => e2 n m
  simp only [e2']
  rw [ie_sum]
  have e1 : ∀ i : Fin N, ∫ a, z (a i) ∂P = charFun μ t := fun i => by rw [hφ]; exact ie_E1 μ z i
  simp only [integral_conj, e1]
  simp only [ie_E1 μ z, ie_E1 μ (fun x => (starRingEnd ℂ) (z x)), integral_conj, ← hφ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, integral_const,
    probReal_univ, one_smul]
  push_cast
  rw [key, key]
  simp only [map_sub, Complex.conj_ofReal]
  field_simp
  ring

theorem iid_ep_expectation (N : ℕ) (hN : 0 < N) (ν μ : Measure ℝ) [IsFiniteMeasure ν]
    [IsProbabilityMeasure μ] :
    iidEP N ν μ = N * discrepancy ν μ + freqMass ν - selfTerm ν μ := by
  set P := Measure.pi fun _ : Fin N => μ
  have hg1 : ∀ t, |gaussCF t| ≤ 1 := by
    intro t; unfold gaussCF
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]; nlinarith [sq_nonneg t]
  have hgc : Continuous gaussCF := by unfold gaussCF; fun_prop
  have hb : ∀ (y : Fin N → ℝ) (t : ℝ),
      ‖(N : ℂ)⁻¹ * ∑ n, Complex.exp (t * y n * I)‖ ≤ 1 := by
    intro y t
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have : ‖∑ n, Complex.exp (t * y n * I)‖ ≤ N := by
      calc _ ≤ ∑ n : Fin N, ‖Complex.exp (t * y n * I)‖ := norm_sum_le _ _
        _ = N := by simp [ie_nz]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    calc (N : ℝ)⁻¹ * ‖∑ n, Complex.exp (t * y n * I)‖ ≤ (N : ℝ)⁻¹ * N :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 1 := inv_mul_cancel₀ hN0.ne'
  set F : (Fin N → ℝ) → ℝ → ℝ := fun y t =>
    (N : ℝ) * ‖(N : ℂ)⁻¹ * ∑ n, Complex.exp (t * y n * I) - (gaussCF t : ℂ)‖ ^ 2 with hF
  have hFb : ∀ y t, ‖F y t‖ ≤ N * 4 := by
    intro y t
    simp only [hF, norm_mul, Real.norm_natCast, norm_pow, norm_norm]
    have h1 : ‖(N : ℂ)⁻¹ * ∑ n, Complex.exp (t * y n * I) - (gaussCF t : ℂ)‖ ≤ 2 := by
      calc _ ≤ ‖(N : ℂ)⁻¹ * ∑ n, Complex.exp (t * y n * I)‖ + ‖(gaussCF t : ℂ)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by
          gcongr
          · exact hb y t
          · rw [Complex.norm_real, Real.norm_eq_abs]; exact hg1 t
        _ = 2 := by norm_num
    have : ‖(N : ℂ)⁻¹ * ∑ n, Complex.exp (t * y n * I) - (gaussCF t : ℂ)‖ ^ 2 ≤ 4 := by
      nlinarith [norm_nonneg ((N : ℂ)⁻¹ * ∑ n, Complex.exp (t * y n * I) - (gaussCF t : ℂ))]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hFc : Continuous (Function.uncurry F) := by
    simp only [hF]; fun_prop
  have hint : Integrable (Function.uncurry F) (P.prod ν) :=
    Integrable.of_bound hFc.aestronglyMeasurable (N * 4) (ae_of_all _ fun p => hFb p.1 p.2)
  have h1 : iidEP N ν μ = ∫ y, ∫ t, F y t ∂ν ∂P := by
    unfold iidEP epStat discrepancy
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [hF, ie_cf]
    rw [integral_const_mul]
  rw [h1, integral_integral_swap hint]
  have h2 : ∀ t, ∫ y, F y t ∂P = N * ‖charFun μ t - gaussCF t‖ ^ 2 + 1 - ‖charFun μ t‖ ^ 2 :=
    fun t => ie_pert N hN μ t (gaussCF t)
  simp only [h2]
  have hcf : Continuous (charFun μ) := continuous_charFun
  have k1 : Integrable (fun t => ‖charFun μ t - gaussCF t‖ ^ 2) ν := by
    refine Integrable.of_bound (by fun_prop) 4 (ae_of_all _ fun t => ?_)
    have : ‖charFun μ t - gaussCF t‖ ≤ 2 := by
      calc _ ≤ ‖charFun μ t‖ + ‖(gaussCF t : ℂ)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by
          gcongr
          · exact norm_charFun_le_one t
          · rw [Complex.norm_real, Real.norm_eq_abs]; exact hg1 t
        _ = 2 := by norm_num
    rw [norm_pow, norm_norm]
    nlinarith [norm_nonneg (charFun μ t - gaussCF t)]
  have k2 : Integrable (fun t => ‖charFun μ t‖ ^ 2) ν := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun t => ?_)
    rw [norm_pow, norm_norm]
    have := norm_charFun_le_one (μ := μ) t
    nlinarith [norm_nonneg (charFun μ t)]
  have k4 : Integrable (fun t => (N : ℝ) * ‖charFun μ t - gaussCF t‖ ^ 2) ν := k1.const_mul _
  have k3 : Integrable (fun t => (N : ℝ) * ‖charFun μ t - gaussCF t‖ ^ 2 + 1) ν :=
    k4.add (integrable_const _)
  rw [integral_sub k3 k2, integral_add k4 (integrable_const _), integral_const_mul, integral_const]
  simp [discrepancy, freqMass, selfTerm, Measure.real]

end GoodViewsNotEnough
open GoodViewsNotEnough in
theorem solution (N : ℕ) (hN : 0 < N) (ν μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsFiniteMeasure ν]
    [MeasureTheory.IsProbabilityMeasure μ] :
    iidEP N ν μ = N * discrepancy ν μ + freqMass ν - selfTerm ν μ :=
  iid_ep_expectation N hN ν μ
