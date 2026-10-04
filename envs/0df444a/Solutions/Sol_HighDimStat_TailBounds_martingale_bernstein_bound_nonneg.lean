-- Prove2me | solution 1 for HighDimStat.TailBounds.martingale_bernstein_bound_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-02T16:32:42.133076+00:00
-- url     : https://prove2.me/submissions/55740453-1951-450e-98d2-d35b1d0f112b

import Mathlib
import Definitions.Def_HighDimStat_TailBounds_IsSubExponential

open MeasureTheory Real HighDimStat.TailBounds

open MeasureTheory ProbabilityTheory Real

namespace GaussianConcentration

set_option maxHeartbeats 800000

/-- A nonnegative integrable variable may multiply a conditional moment bound without
assuming the product integrable in advance. Disintegration supplies that integrability. -/
lemma conditional_product_bound {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : m ≤ mΩ) {F G : Ω → ℝ} {C : ℝ}
    (hFm : Measurable[m] F) (hGm : Measurable G)
    (hFi : Integrable F μ) (hGi : Integrable G μ)
    (hF0 : ∀ ω, 0 ≤ F ω) (hG0 : ∀ ω, 0 ≤ G ω)
    (hbound : μ[G | m] ≤ᵐ[μ] fun _ => C) :
    Integrable (fun ω => F ω * G ω) μ ∧
      (∫ ω, F ω * G ω ∂μ) ≤ C * ∫ ω, F ω ∂μ := by
  letI : MeasurableSpace (Ω × Ω) := m.prod mΩ
  let κ := condExpKernel μ m
  let ν := μ.trim hm
  let H : Ω × Ω → ℝ := fun p => F p.1 * G p.2
  have hH : @Measurable (Ω × Ω) ℝ (m.prod mΩ) _ H :=
    (hFm.comp measurable_fst).mul (hGm.comp measurable_snd)
  have hFν : Integrable F ν := hFi.trim hm hFm.stronglyMeasurable
  have hGκ : ∀ᵐ x ∂ν, Integrable G (κ x) := by
    have h := Measure.ae_integrable_of_integrable_comp
      (show Integrable G (κ ∘ₘ ν) by simpa [κ, ν, condExpKernel_comp_trim hm] using hGi)
    exact h
  have heq : μ[G | m] =ᵐ[ν] fun x => ∫ y, G y ∂κ x :=
    condExp_ae_eq_trim_integral_condExpKernel hm hGi
  have hboundν : μ[G | m] ≤ᵐ[ν] fun _ => C := by
    rw [Filter.EventuallyLE, ae_iff] at hbound ⊢
    rwa [trim_measurableSet_eq hm (by measurability)]
  have hinner : Integrable (fun x => ∫ y, ‖H (x,y)‖ ∂κ x) ν := by
    refine (hFν.mul_const C).mono ?_ ?_
    · exact (hH.stronglyMeasurable.norm.integral_kernel_prod_right').aestronglyMeasurable
    · filter_upwards [heq, hboundν] with x hx hb
      have hn : ∀ y, ‖H (x,y)‖ = F x * G y := by
        intro y
        simp [H, Real.norm_eq_abs, abs_of_nonneg (hF0 x), abs_of_nonneg (hG0 y)]
      simp_rw [hn, integral_const_mul]
      rw [← hx]
      calc
        ‖F x * (μ[G | m]) x‖ ≤ ‖F x * C‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hF0 x) ?_)]
          · exact (mul_le_mul_of_nonneg_left hb (hF0 x)).trans (le_abs_self _)
          · rw [hx]; exact integral_nonneg hG0
        _ = ‖F x * C‖ := rfl
  have hHi : Integrable H (ν ⊗ₘ κ) := by
    refine (Measure.integrable_compProd_iff hH.aestronglyMeasurable).2 ⟨?_, hinner⟩
    filter_upwards [hGκ] with x hx
    exact hx.const_mul (F x)
  have hdiag : @Measurable Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag :=
    (measurable_id'' hm).prodMk measurable_id
  have hprod : Integrable (fun ω => F ω * G ω) μ := by
    have hi : Integrable H (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ) := by
      simpa [κ, ν, compProd_trim_condExpKernel hm] using hHi
    exact hi.comp_measurable hdiag
  refine ⟨hprod, ?_⟩
  calc
    (∫ ω, F ω * G ω ∂μ) = ∫ p, H p ∂(ν ⊗ₘ κ) := by
      rw [show ν ⊗ₘ κ = @Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ
        from compProd_trim_condExpKernel hm]
      rw [integral_map hdiag.aemeasurable hH.aestronglyMeasurable]
      rfl
    _ = ∫ x, F x * ∫ y, G y ∂κ x ∂ν := by
      rw [Measure.integral_compProd hHi]
      simp only [H, integral_const_mul]
    _ ≤ ∫ x, F x * C ∂ν := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ fun x => mul_nonneg (hF0 x) (integral_nonneg hG0)
      · exact hFν.mul_const C
      · filter_upwards [heq, hboundν] with x hx hb
        rw [← hx]
        exact mul_le_mul_of_nonneg_left hb (hF0 x)
    _ = C * ∫ x, F x ∂μ := by
      rw [integral_mul_const, integral_trim hm hFm.stronglyMeasurable]
      ring

end GaussianConcentration

open MeasureTheory ProbabilityTheory Real

namespace GaussianConcentration

set_option maxHeartbeats 800000

lemma admissible_of_le_scale {a A lam : ℝ} (ha : 0 ≤ a) (hA : a ≤ A)
    (hlam : A = 0 ∨ |lam| < 1 / A) : a = 0 ∨ |lam| < 1 / a := by
  by_cases ha0 : a = 0
  · exact Or.inl ha0
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hAp : 0 < A := hap.trans_le hA
  rcases hlam with h | h
  · exact (hAp.ne' h).elim
  · exact Or.inr (h.trans_le (one_div_le_one_div_of_le hap hA))

/-- Conditional MGF bounds add their variance proxies on their common admissible interval.
The result includes integrability, including at zero scale. -/
lemma martingale_sum_mgf {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {D : ℕ → Ω → ℝ} {ν α : ℕ → ℝ} {ℱ : Filtration ℕ mΩ}
    (n : ℕ) (A : ℝ)
    (hα : ∀ k ∈ Finset.Icc 1 n, 0 ≤ α k ∧ α k ≤ A)
    (hm : ∀ k ∈ Finset.Icc 1 n, Measurable[ℱ k] (D k))
    (hi : ∀ k ∈ Finset.Icc 1 n, ∀ lam : ℝ, (α k = 0 ∨ |lam| < 1 / α k) →
      Integrable (fun ω => exp (lam * D k ω)) μ)
    (hb : ∀ k ∈ Finset.Icc 1 n, ∀ lam : ℝ, (α k = 0 ∨ |lam| < 1 / α k) →
      μ[fun ω => exp (lam * D k ω) | ℱ (k - 1)] ≤ᵐ[μ]
        fun _ => exp (lam ^ 2 * (ν k) ^ 2 / 2))
    (lam : ℝ) (hlam : A = 0 ∨ |lam| < 1 / A) :
    Integrable (fun ω => exp (lam * ∑ k ∈ Finset.Icc 1 n, D k ω)) μ ∧
      (∫ ω, exp (lam * ∑ k ∈ Finset.Icc 1 n, D k ω) ∂μ) ≤
        exp (lam ^ 2 * (∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2) / 2) := by
  have main : ∀ j ≤ n,
      Integrable (fun ω => exp (lam * ∑ k ∈ Finset.Icc 1 j, D k ω)) μ ∧
        (∫ ω, exp (lam * ∑ k ∈ Finset.Icc 1 j, D k ω) ∂μ) ≤
          exp (lam ^ 2 * (∑ k ∈ Finset.Icc 1 j, (ν k) ^ 2) / 2) := by
    intro j
    induction j with
    | zero =>
      intro _
      simp
    | succ j ih =>
      intro hj
      have hjn : j ≤ n := by lia
      have hk : j + 1 ∈ Finset.Icc 1 n := by simp; lia
      have hadm := admissible_of_le_scale (hα (j+1) hk).1 (hα (j+1) hk).2 hlam
      have hF : Measurable[ℱ j] (fun ω => exp (lam * ∑ k ∈ Finset.Icc 1 j, D k ω)) := by
        apply Measurable.exp
        apply Measurable.const_mul
        apply Finset.measurable_fun_sum
        intro k hk'
        have hkn : k ∈ Finset.Icc 1 n := by simp at hk' ⊢; lia
        exact (hm k hkn).mono (ℱ.mono (Finset.mem_Icc.mp hk').2) le_rfl
      have hG : Measurable (fun ω => exp (lam * D (j+1) ω)) :=
        (((hm (j+1) hk).mono (ℱ.le (j+1)) le_rfl).const_mul lam).exp
      have step := conditional_product_bound (ℱ.le j) hF hG (ih hjn).1
        (hi (j+1) hk lam hadm) (fun _ => (exp_pos _).le) (fun _ => (exp_pos _).le)
        (by simpa using hb (j+1) hk lam hadm)
      have hsum : ∀ ω, exp (lam * ∑ k ∈ Finset.Icc 1 (j+1), D k ω) =
          exp (lam * ∑ k ∈ Finset.Icc 1 j, D k ω) * exp (lam * D (j+1) ω) := by
        intro ω
        rw [Finset.sum_Icc_succ_top (by lia), mul_add, exp_add]
      refine ⟨by simpa only [hsum] using step.1, ?_⟩
      calc
        _ = ∫ ω, exp (lam * ∑ k ∈ Finset.Icc 1 j, D k ω) * exp (lam * D (j+1) ω) ∂μ := by
          simp only [hsum]
        _ ≤ exp (lam ^ 2 * (ν (j+1)) ^ 2 / 2) *
            ∫ ω, exp (lam * ∑ k ∈ Finset.Icc 1 j, D k ω) ∂μ := step.2
        _ ≤ exp (lam ^ 2 * (ν (j+1)) ^ 2 / 2) *
            exp (lam ^ 2 * (∑ k ∈ Finset.Icc 1 j, (ν k) ^ 2) / 2) := by
          exact mul_le_mul_of_nonneg_left (ih hjn).2 (exp_pos _).le
        _ = _ := by
          rw [Finset.sum_Icc_succ_top (by lia), ← exp_add]
          congr 1
          ring
  exact main n le_rfl

end GaussianConcentration

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped Topology

namespace GaussianConcentration

set_option maxHeartbeats 800000

lemma two_sided_chernoff {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (Z : Ω → ℝ) {V s t : ℝ}
    (hs : 0 ≤ s)
    (hp : Integrable (fun ω => exp (s * Z ω)) μ)
    (hn : Integrable (fun ω => exp (-s * Z ω)) μ)
    (hbp : (∫ ω, exp (s * Z ω) ∂μ) ≤ exp (V * s ^ 2 / 2))
    (hbn : (∫ ω, exp (-s * Z ω) ∂μ) ≤ exp (V * s ^ 2 / 2)) :
    μ.real {ω | t ≤ |Z ω|} ≤ 2 * exp (-s * t + V * s ^ 2 / 2) := by
  have hup : μ.real {ω | t ≤ Z ω} ≤ exp (-s*t + V*s^2/2) := by
    calc
      _ ≤ exp (-s*t) * mgf Z μ s := measure_ge_le_exp_mul_mgf t hs hp
      _ ≤ exp (-s*t) * exp (V*s^2/2) := mul_le_mul_of_nonneg_left hbp (exp_pos _).le
      _ = _ := (exp_add _ _).symm
  have hlo : μ.real {ω | t ≤ -Z ω} ≤ exp (-s*t + V*s^2/2) := by
    have hi : Integrable (fun ω => exp (s * (-Z ω))) μ := by
      simpa only [neg_mul, mul_neg] using hn
    have hb : mgf (fun ω => -Z ω) μ s ≤ exp (V*s^2/2) := by
      simpa only [mgf, neg_mul, mul_neg] using hbn
    calc
      _ ≤ exp (-s*t) * mgf (fun ω => -Z ω) μ s := measure_ge_le_exp_mul_mgf t hs hi
      _ ≤ exp (-s*t) * exp (V*s^2/2) := mul_le_mul_of_nonneg_left hb (exp_pos _).le
      _ = _ := (exp_add _ _).symm
  calc
    _ ≤ μ.real ({ω | t ≤ Z ω} ∪ {ω | t ≤ -Z ω}) := by
      exact measureReal_mono (by
        intro ω hω
        change t ≤ |Z ω| at hω
        change t ≤ Z ω ∨ t ≤ -Z ω
        exact le_abs.mp hω)
    _ ≤ μ.real {ω | t ≤ Z ω} + μ.real {ω | t ≤ -Z ω} := measureReal_union_le _ _
    _ ≤ _ := by linarith

/-- The Chernoff bound extends continuously to the boundary of an open MGF interval.
No boundary exponential integrability is asserted or assumed. -/
lemma two_sided_chernoff_boundary {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (Z : Ω → ℝ) {V A s t : ℝ}
    (hs : 0 < s) (hsA : s ≤ 1 / A)
    (hmgf : ∀ lam : ℝ, |lam| < 1 / A →
      Integrable (fun ω => exp (lam * Z ω)) μ ∧
        (∫ ω, exp (lam * Z ω) ∂μ) ≤ exp (V * lam ^ 2 / 2)) :
    μ.real {ω | t ≤ |Z ω|} ≤ 2 * exp (-s * t + V * s ^ 2 / 2) := by
  haveI : NeBot (𝓝[Ioo 0 s] s) := right_nhdsWithin_Ioo_neBot hs
  have hc : Continuous (fun r : ℝ => 2 * exp (-r*t + V*r^2/2)) := by fun_prop
  have hlim : Tendsto (fun r : ℝ => 2 * exp (-r*t + V*r^2/2))
      (𝓝[Ioo 0 s] s) (𝓝 (2 * exp (-s*t + V*s^2/2))) :=
    hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hradm : |r| < 1 / A := by
    rw [abs_of_pos hr.1]
    exact hr.2.trans_le hsA
  have hnradm : |-r| < 1 / A := by simpa using hradm
  have hp := hmgf r hradm
  have hn := hmgf (-r) hnradm
  apply two_sided_chernoff Z hr.1.le hp.1 hn.1 hp.2
  simpa only [neg_sq] using hn.2

/-- The exact two-regime Bernstein bound, with zero scale and zero variance retained. -/
lemma bernstein_tail_from_mgf {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (Z : Ω → ℝ) {V A : ℝ}
    (hV : 0 ≤ V) (hA : 0 ≤ A)
    (hmgf : ∀ lam : ℝ, (A = 0 ∨ |lam| < 1 / A) →
      Integrable (fun ω => exp (lam * Z ω)) μ ∧
        (∫ ω, exp (lam * Z ω) ∂μ) ≤ exp (V * lam ^ 2 / 2))
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |Z ω|} ≤
      if t ≤ V / A then 2 * exp (-(t ^ 2) / (2 * V))
      else 2 * exp (-t / (2 * A)) := by
  by_cases ht0 : t = 0
  · simp only [ht0, zero_pow (by decide : 2 ≠ 0), neg_zero, zero_div, exp_zero, mul_one,
      ite_self]
    exact measureReal_le_one.trans (by norm_num)
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  by_cases hA0 : A = 0
  · simp only [hA0, div_zero, not_le.mpr htp, ↓reduceIte, mul_zero, neg_div, div_zero,
      neg_zero, exp_zero, mul_one]
    exact measureReal_le_one.trans (by norm_num)
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  have hmgf' : ∀ lam : ℝ, |lam| < 1 / A →
      Integrable (fun ω => exp (lam * Z ω)) μ ∧
        (∫ ω, exp (lam * Z ω) ∂μ) ≤ exp (V * lam ^ 2 / 2) :=
    fun lam h => hmgf lam (Or.inr h)
  split_ifs with hsmall
  · have hcost : t * A ≤ V := (le_div_iff₀ hAp).mp hsmall
    have hVp : 0 < V := (mul_pos htp hAp).trans_le hcost
    have hs : 0 < t / V := div_pos htp hVp
    have hsA : t / V ≤ 1 / A := (div_le_div_iff₀ hVp hAp).2 (by simpa using hcost)
    have hbound := two_sided_chernoff_boundary Z hs hsA hmgf' (t := t)
    have he : -(t/V)*t + V*(t/V)^2/2 = -(t^2)/(2*V) := by field_simp <;> ring
    simpa only [he] using hbound
  · have hlarge : V < t * A := by
      exact (div_lt_iff₀ hAp).mp (lt_of_not_ge hsmall)
    have hbound := two_sided_chernoff_boundary Z (one_div_pos.mpr hAp) le_rfl hmgf' (t := t)
    apply hbound.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
    apply exp_le_exp.mpr
    have he : -(1/A)*t + V*(1/A)^2/2 = (-2*t*A+V)/(2*A^2) := by field_simp <;> ring
    rw [he]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*A^2)).2
    have he' : -t/(2*A)*(2*A^2) = -t*A := by field_simp <;> ring
    rw [he']
    linarith

end GaussianConcentration

theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {D : ℕ → Ω → ℝ} {ν α : ℕ → ℝ} {ℱ : Filtration ℕ mΩ}
    (n : ℕ) (hn : 1 ≤ n)
    (h_alpha : ∀ k ∈ Finset.Icc 1 n, 0 ≤ α k)
    (h_meas : ∀ k ∈ Finset.Icc 1 n, Measurable[ℱ k] (D k))
    (h_int : ∀ k ∈ Finset.Icc 1 n, Integrable (D k) μ)
    (h_cent : ∀ k ∈ Finset.Icc 1 n, μ[D k | ℱ (k - 1)] =ᵐ[μ] 0)
    (h_subexp_int : ∀ k ∈ Finset.Icc 1 n, ∀ lam : ℝ, (α k = 0 ∨ |lam| < 1 / α k) →
      Integrable (fun ω => Real.exp (lam * D k ω)) μ)
    (h_subexp : ∀ k ∈ Finset.Icc 1 n, ∀ lam : ℝ, (α k = 0 ∨ |lam| < 1 / α k) →
      (μ[fun ω => Real.exp (lam * D k ω) | ℱ (k - 1)]) ≤ᵐ[μ]
        fun _ => Real.exp (lam ^ 2 * (ν k) ^ 2 / 2)) :
    IsSubExponential (fun ω => ∑ k ∈ Finset.Icc 1 n, D k ω) μ
        (Real.sqrt (∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2))
        (Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α)
    ∧
    ∀ t : ℝ, 0 ≤ t →
      μ.real {ω | t ≤ |∑ k ∈ Finset.Icc 1 n, D k ω|} ≤
        if t ≤ (∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2) / (Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α)
        then 2 * Real.exp (-(t ^ 2) / (2 * ∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2))
        else 2 * Real.exp (-t / (2 * Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α)) := by
  let V : ℝ := ∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2
  let A : ℝ := Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α
  have hV : 0 ≤ V := Finset.sum_nonneg (fun k _ => sq_nonneg (ν k))
  have hsqrt : (Real.sqrt (∑ k ∈ Finset.Icc 1 n, (ν k)^2))^2 = V := Real.sq_sqrt hV
  have hAm : ∀ k ∈ Finset.Icc 1 n, α k ≤ A := by
    intro k hk
    exact Finset.le_sup' α hk
  have hA : 0 ≤ A := (h_alpha 1 (by simp; exact hn)).trans (hAm 1 (by simp; exact hn))
  have hsumInt : Integrable (fun ω => ∑ k ∈ Finset.Icc 1 n, D k ω) μ := by
    exact integrable_finsetSum _ h_int
  have hmean : ∀ k ∈ Finset.Icc 1 n, ∫ ω, D k ω ∂μ = 0 := by
    intro k hk
    rw [← integral_condExp (ℱ.le (k-1)), integral_congr_ae (h_cent k hk)]
    simp
  have hsumMean : (∫ ω, ∑ k ∈ Finset.Icc 1 n, D k ω ∂μ) = 0 := by
    rw [integral_finsetSum _ h_int]
    exact Finset.sum_eq_zero hmean
  have hmgf : ∀ lam : ℝ, (A = 0 ∨ |lam| < 1 / A) →
      Integrable (fun ω => exp (lam * ∑ k ∈ Finset.Icc 1 n, D k ω)) μ ∧
        (∫ ω, exp (lam * ∑ k ∈ Finset.Icc 1 n, D k ω) ∂μ) ≤ exp (V * lam ^ 2 / 2) := by
    intro lam hlam
    have h := GaussianConcentration.martingale_sum_mgf n A
      (fun k hk => ⟨h_alpha k hk, hAm k hk⟩) h_meas h_subexp_int h_subexp lam hlam
    simpa only [V, mul_comm (lam^2)] using h
  constructor
  · unfold IsSubExponential
    refine ⟨hsumInt, ?_, ?_⟩
    · intro lam hlam
      simpa only [hsumMean, sub_zero] using (hmgf lam hlam).1
    · intro lam hlam
      simpa only [hsumMean, sub_zero, hsqrt] using (hmgf lam hlam).2
  · intro t ht
    exact GaussianConcentration.bernstein_tail_from_mgf _ hV hA hmgf ht

#print axioms solution
