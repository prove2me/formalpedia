-- Prove2me | solution 1 for ManyServerFluid.Equilibrium.remark_3_8
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-05T19:17:25.256285+00:00
-- url     : https://prove2.me/submissions/1cbf894d-083a-4eff-8d3e-08d4c97067cb

import Mathlib
import Definitions.Def_ManyServerFluid_Equilibrium_Model
import Definitions.Def_ManyServerFluid_Equilibrium_Renewal

open MeasureTheory Filter Topology Set

namespace R38

lemma hasDerivWithinAt_Ici_of_tendsto {f : ℝ → ℝ} {r d : ℝ}
    (h : Tendsto (fun ε => (f (r + ε) - f r) / ε) (𝓝[>] 0) (𝓝 d)) :
    HasDerivWithinAt f d (Ici r) r := by
  rw [← hasDerivWithinAt_Ioi_iff_Ici, hasDerivWithinAt_iff_tendsto_slope,
    sdiff_singleton_eq_self (show r ∉ Ioi r from lt_irrefl r)]
  have hm : Tendsto (fun y => y - r) (𝓝[>] r) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun y => y - r) (𝓝 r) (𝓝 (r - r)) := tendsto_id.sub tendsto_const_nhds
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simpa using hy
  refine (h.comp hm).congr' ?_
  filter_upwards with y
  simp [slope_def_field, Function.comp]

/-- averages of a continuous function along a shrinking segment -/
lemma tendsto_avg (Φ : ℝ × ℝ → ℝ) (hΦ : Continuous Φ) (x0 s : ℝ) :
    Tendsto (fun ε => ε⁻¹ * ∫ u in x0..x0 + ε, Φ (u, s + ε)) (𝓝[>] 0) (𝓝 (Φ (x0, s))) := by
  have key : ∀ ε : ℝ, ε ≠ 0 →
      ε⁻¹ * ∫ u in x0..x0 + ε, Φ (u, s + ε) = ∫ v in (0:ℝ)..1, Φ (ε * v + x0, s + ε) := by
    intro ε hε
    rw [intervalIntegral.integral_comp_mul_add (fun u => Φ (u, s + ε)) hε]
    simp [smul_eq_mul, add_comm]
  have hc : Continuous fun ε : ℝ => ∫ v in (0:ℝ)..1, Φ (ε * v + x0, s + ε) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hΦ.comp (by fun_prop)
  have h0 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  simp only [zero_mul, zero_add, add_zero, intervalIntegral.integral_const, sub_zero,
    smul_eq_mul, one_mul] at h0
  refine h0.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (key ε (ne_of_gt hε)).symm


section Core
variable (Φ DΦ : ℝ × ℝ → ℝ) (hΦ : Continuous Φ) (hDΦ : Continuous DΦ) (b τ : ℝ)
  (hD : ∀ x s, 0 ≤ x → x < b → 0 ≤ s → s < τ →
    Tendsto (fun ε => (Φ (x + ε, s + ε) - Φ (x, s)) / ε) (𝓝[>] 0) (𝓝 (DΦ (x, s))))
include hD

lemma quot_bound {C : ℝ} (hC : ∀ p ∈ Icc 0 b ×ˢ Icc 0 τ, |DΦ p| ≤ C) (hΦ : Continuous Φ)
    {x s ε : ℝ} (hx : 0 ≤ x) (hs : 0 ≤ s) (hε : 0 ≤ ε) (hxb : x + ε < b) (hst : s + ε < τ) :
    |Φ (x + ε, s + ε) - Φ (x, s)| ≤ C * ε := by
  have := norm_image_sub_le_of_norm_deriv_right_le_segment (a := 0) (b := ε)
    (f := fun r => Φ (x + r, s + r)) (f' := fun r => DΦ (x + r, s + r)) (C := C)
    (hΦ.comp (by fun_prop)).continuousOn ?_ ?_ ε ⟨hε, le_rfl⟩
  · simpa using this
  · intro r hr
    apply hasDerivWithinAt_Ici_of_tendsto
    have := hD (x + r) (s + r) (by linarith [hr.1]) (by linarith [hr.2]) (by linarith [hr.1])
      (by linarith [hr.2])
    simpa [add_assoc] using this
  · intro r hr
    exact hC _ ⟨⟨by simp; linarith [hr.1], by simp; linarith [hr.2]⟩,
      ⟨by simp; linarith [hr.1], by simp; linarith [hr.2]⟩⟩


lemma deriv_J (hΦ : Continuous Φ) (hDΦ : Continuous DΦ) {a s : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hs : 0 ≤ s) (hsτ : s < τ) :
    HasDerivWithinAt (fun s => ∫ x in (0:ℝ)..a, Φ (x, s))
      ((∫ x in (0:ℝ)..a, DΦ (x, s)) + Φ (0, s) - Φ (a, s)) (Ici s) s := by
  apply hasDerivWithinAt_Ici_of_tendsto
  -- bound for DΦ on the compact rectangle
  obtain ⟨C, hC⟩ : ∃ C, ∀ p ∈ Icc 0 b ×ˢ Icc 0 τ, |DΦ p| ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
      hDΦ.continuousOn
    exact ⟨C, fun p hp => by simpa using hC p hp⟩
  set ε0 := min (b - a) (τ - s) with hε0
  have hε0pos : 0 < ε0 := lt_min (by linarith) (by linarith)
  have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε ∈ Ioo 0 ε0 :=
    Ioo_mem_nhdsGT hε0pos
  -- the three pieces
  have h1 : Tendsto (fun ε => ∫ x in (0:ℝ)..a, (Φ (x + ε, s + ε) - Φ (x, s)) / ε) (𝓝[>] 0)
      (𝓝 (∫ x in (0:ℝ)..a, DΦ (x, s))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    · filter_upwards with ε
      exact ((Continuous.div_const (by
        exact (hΦ.comp (by fun_prop)).sub (hΦ.comp (by fun_prop))) ε)).aestronglyMeasurable
    · filter_upwards [hev] with ε hε
      filter_upwards with x hx
      rw [uIoc_of_le ha] at hx
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hε.1, div_le_iff₀ hε.1]
      exact quot_bound Φ DΦ b τ hD hC hΦ hx.1.le hs hε.1.le
        (by linarith [hx.2, hε.2, min_le_left (b - a) (τ - s)])
        (by linarith [hε.2, min_le_right (b - a) (τ - s)])
    · exact intervalIntegrable_const
    · filter_upwards with x hx
      rw [uIoc_of_le ha] at hx
      exact hD x s hx.1.le (by linarith [hx.2]) hs hsτ
  have h2 := tendsto_avg Φ hΦ 0 s
  have h3 := tendsto_avg Φ hΦ a s
  have hsum := (h1.add h2).sub h3
  refine hsum.congr' ?_
  filter_upwards [hev] with ε hε
  have hεne : ε ≠ 0 := ne_of_gt hε.1
  have hcF : Continuous fun x => Φ (x + ε, s + ε) := hΦ.comp (by fun_prop)
  have eJ : (∫ x in (0:ℝ)..a, Φ (x, s + ε)) =
      ∫ x in (-ε)..(a - ε), Φ (x + ε, s + ε) := by
    rw [intervalIntegral.integral_comp_add_right (fun x => Φ (x, s + ε))]
    simp
  have esplit : (∫ x in (-ε)..(a - ε), Φ (x + ε, s + ε)) =
      (∫ x in (-ε)..0, Φ (x + ε, s + ε)) + (∫ x in (0:ℝ)..a, Φ (x + ε, s + ε))
        - ∫ x in (a - ε)..a, Φ (x + ε, s + ε) := by
    have i1 := intervalIntegral.integral_add_adjacent_intervals
      (hcF.intervalIntegrable (μ := volume) (-ε) 0) (hcF.intervalIntegrable (μ := volume) 0 (a - ε))
    have i2 := intervalIntegral.integral_add_adjacent_intervals
      (hcF.intervalIntegrable (μ := volume) 0 (a - ε)) (hcF.intervalIntegrable (μ := volume) (a - ε) a)
    linarith
  have eL : (∫ x in (-ε)..0, Φ (x + ε, s + ε)) = ∫ u in (0:ℝ)..0 + ε, Φ (u, s + ε) := by
    rw [intervalIntegral.integral_comp_add_right (fun x => Φ (x, s + ε))]
    simp
  have eR : (∫ x in (a - ε)..a, Φ (x + ε, s + ε)) = ∫ u in a..a + ε, Φ (u, s + ε) := by
    rw [intervalIntegral.integral_comp_add_right (fun x => Φ (x, s + ε))]
    simp
  have eQ : (∫ x in (0:ℝ)..a, (Φ (x + ε, s + ε) - Φ (x, s)) / ε) =
      ((∫ x in (0:ℝ)..a, Φ (x + ε, s + ε)) - ∫ x in (0:ℝ)..a, Φ (x, s)) / ε := by
    have hc2 : Continuous fun x : ℝ => Φ (x, s) := hΦ.comp (by fun_prop)
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
      (hcF.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
  rw [eQ, ← eL, ← eR, eJ, esplit]
  field_simp
  ring


lemma core_A (hΦ : Continuous Φ) (hDΦ : Continuous DΦ) {a t : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (ht : 0 ≤ t) (htτ : t < τ) :
    (∫ x in (0:ℝ)..a, Φ (x, t)) - (∫ x in (0:ℝ)..a, Φ (x, 0)) =
      ∫ s in (0:ℝ)..t, ((∫ x in (0:ℝ)..a, DΦ (x, s)) + Φ (0, s) - Φ (a, s)) := by
  have hJc : Continuous fun s : ℝ => ∫ x in (0:ℝ)..a, Φ (x, s) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hΦ.comp (by fun_prop)
  have hJ'c : Continuous fun s : ℝ => (∫ x in (0:ℝ)..a, DΦ (x, s)) + Φ (0, s) - Φ (a, s) := by
    refine Continuous.sub (Continuous.add ?_ (hΦ.comp (by fun_prop))) (hΦ.comp (by fun_prop))
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hDΦ.comp (by fun_prop)
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hJc.continuousOn
  · intro s hs
    exact (deriv_J Φ DΦ b τ hD hΦ hDΦ ha hab hs.1.le (by linarith [hs.2])).mono Ioi_subset_Ici_self
  · exact hJ'c.intervalIntegrable _ _

end Core

lemma lemB (g : ℝ → ℝ) (hg_meas : Measurable g) (hg_int : Integrable g) (hg_nn : ∀ y, 0 ≤ g y)
    (hg0 : ∀ y, y < 0 → g y = 0) (ψ : ℝ → ℝ) (hψ : Continuous ψ) (C : ℝ)
    (hC : ∀ x, |ψ x| ≤ C) {m1 : ℝ} (hm1 : 0 ≤ m1) :
    ∫ y, g y * ∫ x in (0:ℝ)..(min (max y 0) m1), ψ x =
      ∫ x in (0:ℝ)..m1, ψ x * ∫ y in Ioi x, g y := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  set F : ℝ → ℝ → ℝ := fun y x => g y * (if x ≤ y then ψ x else 0) with hF
  have step1 : ∀ y, g y * ∫ x in (0:ℝ)..(min (max y 0) m1), ψ x =
      ∫ x in Ioc 0 m1, F y x := by
    intro y
    rcases lt_or_ge y 0 with hy | hy
    · simp [hF, hg0 y hy]
    · have hmin : 0 ≤ min y m1 := le_min hy hm1
      rw [max_eq_left hy, intervalIntegral.integral_of_le hmin, ← integral_const_mul]
      have : ∀ x, F y x = (Iic y).indicator (fun x => g y * ψ x) x := by
        intro x; simp [hF, Set.indicator_apply, mul_ite]
      simp_rw [this]
      rw [setIntegral_indicator measurableSet_Iic]
      congr 2
      ext x; simp only [mem_inter_iff, mem_Ioc, mem_Iic, le_min_iff]; tauto
  have hint : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Ioc (0:ℝ) m1))) := by
    refine Integrable.mono' (hg_int.mul_prod (integrable_const C)) ?_ ?_
    · apply Measurable.aestronglyMeasurable
      apply Measurable.mul (hg_meas.comp measurable_fst)
      exact Measurable.ite (measurableSet_le measurable_snd measurable_fst)
        (hψ.measurable.comp measurable_snd) measurable_const
    · filter_upwards with p
      simp only [Function.uncurry, hF, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg_nn _)]
      apply mul_le_mul_of_nonneg_left _ (hg_nn _)
      split_ifs
      · exact hC _
      · simpa using hC0
  simp_rw [step1]
  rw [integral_integral_swap hint, intervalIntegral.integral_of_le hm1]
  congr 1
  ext x
  have : ∀ y, F y x = (Ici x).indicator (fun y => g y * ψ x) y := by
    intro y; simp [hF, Set.indicator_apply, mul_ite]
  simp_rw [this]
  rw [integral_indicator measurableSet_Ici, integral_mul_const, integral_Ici_eq_integral_Ioi]
  ring


lemma lemF (g : ℝ → ℝ) (hg_meas : Measurable g) (hg_int : Integrable g) (hg_nn : ∀ y, 0 ≤ g y)
    (K : ℝ → ℝ → ℝ) (hK : Continuous (Function.uncurry K)) (C : ℝ)
    (hC : ∀ y s, |K y s| ≤ C) {t : ℝ} (ht : 0 ≤ t) :
    ∫ y, g y * ∫ s in (0:ℝ)..t, K y s = ∫ s in (0:ℝ)..t, ∫ y, g y * K y s := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0 0)
  simp_rw [intervalIntegral.integral_of_le ht, ← integral_const_mul]
  apply integral_integral_swap
  refine Integrable.mono' (hg_int.mul_prod (integrable_const C)) ?_ ?_
  · apply Measurable.aestronglyMeasurable
    exact Measurable.mul (hg_meas.comp measurable_fst) hK.measurable
  · filter_upwards with p
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg_nn _)]
    exact mul_le_mul_of_nonneg_left (hC _ _) (hg_nn _)

lemma integrable_g_mul (g : ℝ → ℝ) (hg_int : Integrable g) (h : ℝ → ℝ) (hh : Continuous h)
    (C : ℝ) (hC : ∀ y, |h y| ≤ C) : Integrable (fun y => g y * h y) := by
  have := hg_int.mul_bdd (g := h) (c := C) hh.aestronglyMeasurable
    (Eventually.of_forall fun y => by simpa using hC y)
  exact this

section W
variable (Φ DΦ : ℝ × ℝ → ℝ) (hΦ : Continuous Φ) (hDΦ : Continuous DΦ) (b τ : ℝ)
  (hD : ∀ x s, 0 ≤ x → x < b → 0 ≤ s → s < τ →
    Tendsto (fun ε => (Φ (x + ε, s + ε) - Φ (x, s)) / ε) (𝓝[>] 0) (𝓝 (DΦ (x, s))))
  (C : ℝ) (hCΦ : ∀ p, |Φ p| ≤ C) (hCD : ∀ p, |DΦ p| ≤ C)
  (g : ℝ → ℝ) (hg_meas : Measurable g) (hg_int : Integrable g) (hg_nn : ∀ y, 0 ≤ g y)
  (hg0 : ∀ y, y < 0 → g y = 0) (hg1 : ∫ y, g y = 1)
include hD hΦ hDΦ hCΦ hCD hg_meas hg_int hg_nn hg0 hg1

lemma core_W {m1 t : ℝ} (hm1 : 0 ≤ m1) (hm1b : m1 < b) (ht : 0 ≤ t) (htτ : t < τ)
    (hzero : ∀ s, 0 ≤ s → s ≤ t → Φ (m1, s) = 0) :
    (∫ x in (0:ℝ)..m1, Φ (x, t) * ∫ y in Ioi x, g y) =
      (∫ x in (0:ℝ)..m1, Φ (x, 0) * ∫ y in Ioi x, g y)
      + (∫ s in (0:ℝ)..t, ∫ x in (0:ℝ)..m1, DΦ (x, s) * ∫ y in Ioi x, g y)
      - (∫ s in (0:ℝ)..t, ∫ x in (0:ℝ)..m1, g x * Φ (x, s))
      + ∫ s in (0:ℝ)..t, Φ (0, s) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hCΦ 0)
  set a : ℝ → ℝ := fun y => min (max y 0) m1 with ha
  have ha0 : ∀ y, 0 ≤ a y := fun y => le_min (le_max_right _ _) hm1
  have ham : ∀ y, a y ≤ m1 := fun y => min_le_right _ _
  have hac : Continuous a := by fun_prop
  -- pointwise identity
  have hA : ∀ y, (∫ x in (0:ℝ)..a y, Φ (x, t)) - (∫ x in (0:ℝ)..a y, Φ (x, 0)) =
      (∫ s in (0:ℝ)..t, ∫ x in (0:ℝ)..a y, DΦ (x, s)) + (∫ s in (0:ℝ)..t, Φ (0, s))
        - ∫ s in (0:ℝ)..t, Φ (a y, s) := by
    intro y
    rw [core_A Φ DΦ b τ hD hΦ hDΦ (ha0 y) (lt_of_le_of_lt (ham y) hm1b) ht htτ]
    have c1 : Continuous fun s : ℝ => ∫ x in (0:ℝ)..a y, DΦ (x, s) := by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      exact hDΦ.comp (by fun_prop)
    have c2 : Continuous fun s : ℝ => Φ (0, s) := hΦ.comp (by fun_prop)
    have c3 : Continuous fun s : ℝ => Φ (a y, s) := hΦ.comp (by fun_prop)
    have := intervalIntegral.integral_sub (μ := volume) (a := 0) (b := t)
      ((c1.add c2).intervalIntegrable _ _) (c3.intervalIntegrable _ _)
    have h2 := intervalIntegral.integral_add (μ := volume) (a := 0) (b := t)
      (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _)
    simp only [Pi.add_apply] at this h2
    rw [this, h2]
  -- bounds
  have bdI : ∀ (ψ : ℝ → ℝ), (∀ x, |ψ x| ≤ C) → ∀ y, |∫ x in (0:ℝ)..a y, ψ x| ≤ C * m1 := by
    intro ψ hψ y
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := a y) (C := C)
      (f := ψ) (fun x _ => by simpa using hψ x)
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg (ha0 y)] at this
    exact this.trans (mul_le_mul_of_nonneg_left (ham y) hC0)
  have contI : ∀ (F : ℝ × ℝ → ℝ), Continuous F → Continuous fun p : ℝ × ℝ =>
      ∫ x in (0:ℝ)..a p.1, F (x, p.2) := by
    intro F hF
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℝ × ℝ) (x : ℝ) => F (x, p.2))
    · exact hF.comp (by fun_prop)
    · exact hac.comp continuous_fst
  -- the four y-integrals
  have eT : ∀ r, ∫ y, g y * ∫ x in (0:ℝ)..a y, Φ (x, r) =
      ∫ x in (0:ℝ)..m1, Φ (x, r) * ∫ y in Ioi x, g y := fun r =>
    lemB g hg_meas hg_int hg_nn hg0 (fun x => Φ (x, r)) (hΦ.comp (by fun_prop)) C
      (fun x => hCΦ _) hm1
  have eD : ∫ y, g y * ∫ s in (0:ℝ)..t, ∫ x in (0:ℝ)..a y, DΦ (x, s) =
      ∫ s in (0:ℝ)..t, ∫ x in (0:ℝ)..m1, DΦ (x, s) * ∫ y in Ioi x, g y := by
    rw [lemF g hg_meas hg_int hg_nn (fun y s => ∫ x in (0:ℝ)..a y, DΦ (x, s))
      ((contI DΦ hDΦ).comp continuous_id) (C * m1) (fun y s => bdI _ (fun x => hCD _) y) ht]
    congr 1; ext s
    exact lemB g hg_meas hg_int hg_nn hg0 (fun x => DΦ (x, s)) (hDΦ.comp (by fun_prop)) C
      (fun x => hCD _) hm1
  have eP : ∫ y, g y * ∫ s in (0:ℝ)..t, Φ (a y, s) =
      ∫ s in (0:ℝ)..t, ∫ x in (0:ℝ)..m1, g x * Φ (x, s) := by
    rw [lemF g hg_meas hg_int hg_nn (fun y s => Φ (a y, s))
      (hΦ.comp (by fun_prop)) C (fun y s => hCΦ _) ht]
    rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le ht]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    simp only
    rw [intervalIntegral.integral_of_le hm1, ← integral_Icc_eq_integral_Ioc,
      ← integral_indicator measurableSet_Icc]
    congr 1; ext y
    simp only [Set.indicator_apply, mem_Icc, ha]
    split_ifs with hy
    · rw [max_eq_left hy.1, min_eq_left hy.2]
    · rcases lt_or_ge y 0 with hy0 | hy0
      · simp [hg0 y hy0]
      · have : m1 < y := by
          by_contra h; exact hy ⟨hy0, not_lt.mp h⟩
        rw [max_eq_left hy0, min_eq_right this.le, hzero s hs.1.le hs.2, mul_zero]
  have e0 : ∫ y, g y * ∫ s in (0:ℝ)..t, Φ (0, s) = ∫ s in (0:ℝ)..t, Φ (0, s) := by
    rw [integral_mul_const, hg1, one_mul]
  -- integrate hA against g
  have hint : ∀ (h : ℝ → ℝ), Continuous h → (∃ C', ∀ y, |h y| ≤ C') →
      Integrable (fun y => g y * h y) := by
    rintro h hh ⟨C', hC'⟩
    exact integrable_g_mul g hg_int h hh C' hC'
  have iT : ∀ r, Integrable (fun y => g y * ∫ x in (0:ℝ)..a y, Φ (x, r)) := by
    intro r
    refine hint _ ((contI Φ hΦ).comp (by fun_prop : Continuous fun y : ℝ => (y, r)))
      ⟨C * m1, fun y => bdI _ (fun x => hCΦ _) y⟩
  have iD : Integrable (fun y => g y * ∫ s in (0:ℝ)..t, ∫ x in (0:ℝ)..a y, DΦ (x, s)) := by
    refine hint _ ?_ ⟨C * m1 * t, fun y => ?_⟩
    · apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      exact (contI DΦ hDΦ).comp (by fun_prop)
    · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := C * m1)
        (f := fun s => ∫ x in (0:ℝ)..a y, DΦ (x, s)) (fun s _ => by
          simpa using bdI _ (fun x => hCD _) y)
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] at this
      exact this
  have iP : Integrable (fun y => g y * ∫ s in (0:ℝ)..t, Φ (a y, s)) := by
    refine hint _ ?_ ⟨C * t, fun y => ?_⟩
    · apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      exact hΦ.comp (by fun_prop)
    · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := C)
        (f := fun s => Φ (a y, s)) (fun s _ => by simpa using hCΦ _)
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] at this
      exact this
  have i0 : Integrable (fun y => g y * ∫ s in (0:ℝ)..t, Φ (0, s)) := hg_int.mul_const _
  have key : ∫ y, g y * ((∫ x in (0:ℝ)..a y, Φ (x, t)) - (∫ x in (0:ℝ)..a y, Φ (x, 0))) =
      ∫ y, g y * ((∫ s in (0:ℝ)..t, ∫ x in (0:ℝ)..a y, DΦ (x, s)) + (∫ s in (0:ℝ)..t, Φ (0, s))
        - ∫ s in (0:ℝ)..t, Φ (a y, s)) := by
    congr 1; ext y; rw [hA y]
  simp only [mul_sub, mul_add] at key
  have s1 := integral_sub (iD.add i0) iP
  have s2 := integral_add iD i0
  simp only [Pi.add_apply] at s1 s2
  rw [integral_sub (iT t) (iT 0), s1, s2, eT, eT, eD, eP, e0] at key
  linarith

end W
end R38


open MeasureTheory Filter Topology Set

namespace R38
open ManyServerFluid.Equilibrium

variable (S : ServiceLaw)

lemma intOn (s : Set ℝ) : IntegrableOn S.g s := S.integrable_g.integrableOn

lemma one_sub_G (x : ℝ) : 1 - S.G x = ∫ y in Ioi x, S.g y := by
  have := integral_add_compl (measurableSet_Iic (a := x)) S.integrable_g
  rw [compl_Iic, S.integral_g] at this
  simp only [ServiceLaw.G]; linarith

lemma G_le_one (x : ℝ) : S.G x ≤ 1 := by
  have := one_sub_G S x
  have h : 0 ≤ ∫ y in Ioi x, S.g y := setIntegral_nonneg measurableSet_Ioi (fun y _ => S.g_nonneg y)
  linarith

lemma G_mono : Monotone S.G := by
  intro x y hxy
  exact setIntegral_mono_set (intOn S _) (Eventually.of_forall fun z => S.g_nonneg z)
    (Eventually.of_forall (Iic_subset_Iic.mpr hxy))

lemma G_cont : Continuous S.G := by
  have hII : ∀ a b : ℝ, IntervalIntegrable S.g volume a b :=
    fun a b => S.integrable_g.intervalIntegrable
  have h := intervalIntegral.continuous_primitive hII 0
  have e : S.G = fun x => S.G 0 + ∫ y in (0:ℝ)..x, S.g y := by
    ext x
    simp only [ServiceLaw.G]
    rw [← intervalIntegral.integral_Iic_sub_Iic (intOn S _) (intOn S _)]
    ring
  rw [e]; exact continuous_const.add h

lemma G_lt_one_of_mem {x : ℝ} (hx : x ∈ S.Ages) : S.G x < 1 := by
  obtain ⟨hx0, hxM⟩ := hx
  simp only [ServiceLaw.M] at hxM
  obtain ⟨y, hy⟩ := lt_iSup_iff.mp hxM
  obtain ⟨⟨hy0, hyG⟩, hy'⟩ := lt_iSup_iff.mp hy
  have : x < y := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hx0).mp hy'
  exact lt_of_le_of_lt (G_mono S this.le) hyG

lemma mem_of_G_lt_one {x : ℝ} (hx0 : 0 ≤ x) (hG : S.G x < 1) : x ∈ S.Ages := by
  refine ⟨hx0, ?_⟩
  have hc := (G_cont S).continuousAt (x := x)
  have : ∀ᶠ y in 𝓝 x, S.G y < 1 := hc.eventually (gt_mem_nhds hG)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp this
  have hy : S.G (x + δ / 2) < 1 := hball (by
    rw [Real.dist_eq]; rw [abs_of_nonneg (by linarith)]; linarith)
  have hle : ENNReal.ofReal (x + δ / 2) ≤ S.M := by
    simp only [ServiceLaw.M]
    exact le_iSup₂_of_le (f := fun (y : ℝ) (_ : 0 ≤ y ∧ S.G y < 1) => ENNReal.ofReal y)
      (x + δ / 2) ⟨by linarith, hy⟩ le_rfl
  refine lt_of_lt_of_le ?_ hle
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)

lemma G_eq_one {x : ℝ} (hx0 : 0 ≤ x) (hx : x ∉ S.Ages) : S.G x = 1 := by
  by_contra h
  exact hx (mem_of_G_lt_one S hx0 (lt_of_le_of_ne (G_le_one S x) h))

lemma G_neg {x : ℝ} (hx : x < 0) : S.G x = 0 := by
  simp only [ServiceLaw.G]
  rw [setIntegral_congr_fun measurableSet_Iic (g := fun _ => (0:ℝ))
    (fun y hy => S.g_eq_zero_of_neg y (lt_of_le_of_lt hy hx))]
  simp


lemma w_meas : Measurable fun x => ENNReal.ofReal (1 - S.G x) :=
  ENNReal.measurable_ofReal.comp ((G_cont S).measurable.const_sub 1)

lemma nuStar_integral (f : ℝ → ℝ) :
    ∫ x, f x ∂S.nuStar = ∫ x in Ici 0, (1 - S.G x) * f x := by
  have hm : Measurable fun x => (1 - S.G x).toNNReal :=
    measurable_real_toNNReal.comp ((G_cont S).measurable.const_sub 1)
  have := integral_withDensity_eq_integral_smul (μ := volume.restrict (Ici (0:ℝ))) hm f
  simp only [ServiceLaw.nuStar]
  have e : (fun x => ENNReal.ofReal (1 - S.G x)) = fun x => ((1 - S.G x).toNNReal : ENNReal) := rfl
  rw [e, this]
  congr 1; ext x
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (by linarith [G_le_one S x])]

lemma ages_meas : MeasurableSet S.Ages :=
  (measurableSet_le measurable_const measurable_id).inter
    (measurableSet_lt ENNReal.measurable_ofReal measurable_const)

lemma nuStar_compl : S.nuStar S.Agesᶜ = 0 := by
  simp only [ServiceLaw.nuStar]
  rw [withDensity_apply _ (ages_meas S).compl, Measure.restrict_restrict (ages_meas S).compl]
  apply setLIntegral_eq_zero ((ages_meas S).compl.inter measurableSet_Ici)
  intro x hx
  simp [G_eq_one S hx.2 hx.1]

lemma lintegral_one_sub_G : ∫⁻ x in Ici 0, ENNReal.ofReal (1 - S.G x) = 1 := by
  set μg : Measure ℝ := volume.withDensity fun x => ENNReal.ofReal (S.g x) with hμg
  have hgm : Measurable fun x => ENNReal.ofReal (S.g x) :=
    ENNReal.measurable_ofReal.comp S.measurable_g
  have hnn : 0 ≤ᵐ[μg] (fun x : ℝ => x) := by
    rw [hμg, Filter.EventuallyLE, ae_withDensity_iff hgm]
    filter_upwards with x hx
    by_contra h
    push_neg at h
    exact hx (by simp [S.g_eq_zero_of_neg x h])
  have lc := lintegral_eq_lintegral_meas_lt μg hnn measurable_id.aemeasurable
  have lhs : ∫⁻ x, ENNReal.ofReal x ∂μg = 1 := by
    rw [hμg, lintegral_withDensity_eq_lintegral_mul _ hgm ENNReal.measurable_ofReal]
    have : ∀ x, (fun x => ENNReal.ofReal (S.g x)) x * ENNReal.ofReal x
        = ENNReal.ofReal (x * S.g x) := by
      intro x
      rcases lt_or_ge x 0 with hx | hx
      · simp [S.g_eq_zero_of_neg x hx]
      · rw [mul_comm, ENNReal.ofReal_mul hx]
    simp only [Pi.mul_apply, this]
    rw [← ofReal_integral_eq_lintegral_ofReal S.integrable_mean, S.mean_one, ENNReal.ofReal_one]
    filter_upwards with x
    rcases lt_or_ge x 0 with hx | hx
    · simp [S.g_eq_zero_of_neg x hx]
    · exact mul_nonneg hx (S.g_nonneg x)
  have rhs : ∀ t, μg {a | t < a} = ENNReal.ofReal (1 - S.G t) := by
    intro t
    change μg (Ioi t) = _
    rw [hμg, withDensity_apply _ measurableSet_Ioi, one_sub_G,
      ofReal_integral_eq_lintegral_ofReal (intOn S _) (Eventually.of_forall fun y => S.g_nonneg y)]
  simp only [rhs] at lc
  rw [lhs] at lc
  rw [lc, setLIntegral_congr Ioi_ae_eq_Ici.symm]

lemma nuStar_univ : S.nuStar univ = 1 := by
  simp only [ServiceLaw.nuStar]
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_one_sub_G]


lemma transfer (ψ Ψ : ℝ → ℝ) {m1 : ℝ} (hm1 : 0 ≤ m1) (hsub : Icc 0 m1 ⊆ S.Ages)
    (heq : ∀ x ∈ S.Ages, x ≤ m1 → ψ x = Ψ x) (hz : ∀ x ∈ S.Ages, m1 < x → ψ x = 0) :
    ∫ x in Ici 0, (1 - S.G x) * ψ x = ∫ x in (0:ℝ)..m1, Ψ x * ∫ y in Ioi x, S.g y := by
  rw [setIntegral_congr_fun measurableSet_Ici
    (g := (Icc 0 m1).indicator fun x => (1 - S.G x) * Ψ x)]
  · rw [setIntegral_indicator measurableSet_Icc, inter_eq_right.mpr Icc_subset_Ici_self,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hm1]
    congr 1; ext x; rw [one_sub_G, mul_comm]
  · intro x hx
    simp only [Set.indicator_apply, mem_Icc]
    by_cases hA : x ∈ S.Ages
    · split_ifs with h
      · rw [heq x hA h.2]
      · rw [hz x hA (by push_neg at h; exact h hx), mul_zero]
    · rw [G_eq_one S hx hA, sub_self, zero_mul]
      split_ifs with h
      · exact absurd (hsub h) hA
      · rfl

lemma transfer_h (ψ Ψ : ℝ → ℝ) {m1 : ℝ} (hm1 : 0 ≤ m1) (hsub : Icc 0 m1 ⊆ S.Ages)
    (heq : ∀ x ∈ S.Ages, x ≤ m1 → ψ x = Ψ x) (hz : ∀ x ∈ S.Ages, m1 < x → ψ x = 0) :
    ∫ x in Ici 0, (1 - S.G x) * (S.h x * ψ x) = ∫ x in (0:ℝ)..m1, S.g x * Ψ x := by
  rw [setIntegral_congr_fun measurableSet_Ici
    (g := (Icc 0 m1).indicator fun x => S.g x * Ψ x)]
  · rw [setIntegral_indicator measurableSet_Icc, inter_eq_right.mpr Icc_subset_Ici_self,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hm1]
  · intro x hx
    simp only [Set.indicator_apply, mem_Icc]
    by_cases hA : x ∈ S.Ages
    · have hpos : 0 < 1 - S.G x := by linarith [G_lt_one_of_mem S hA]
      have hh : (1 - S.G x) * S.h x = S.g x := by
        simp only [ServiceLaw.h]; field_simp
      split_ifs with h
      · rw [heq x hA h.2, ← mul_assoc, hh]
      · rw [hz x hA (by push_neg at h; exact h hx), mul_zero, mul_zero]
    · rw [G_eq_one S hx hA, sub_self, zero_mul]
      split_ifs with h
      · exact absurd (hsub h) hA
      · rfl

lemma G_zero : S.G 0 = 0 := by
  simp only [ServiceLaw.G]
  rw [setIntegral_congr_set Iio_ae_eq_Iic.symm]
  rw [setIntegral_congr_fun measurableSet_Iio (g := fun _ => (0:ℝ))
    (fun y hy => S.g_eq_zero_of_neg y hy)]
  simp

lemma h_meas : Measurable S.h :=
  S.measurable_g.div ((G_cont S).measurable.const_sub 1)

lemma lint_h : ∫⁻ x, ENNReal.ofReal (S.h x) ∂S.nuStar = 1 := by
  simp only [ServiceLaw.nuStar]
  have hm : Measurable fun x => ENNReal.ofReal (S.h x) := ENNReal.measurable_ofReal.comp (h_meas S)
  rw [lintegral_withDensity_eq_lintegral_mul _ (w_meas S) hm]
  have e : ∀ x ∈ Ici (0:ℝ), ((fun x => ENNReal.ofReal (1 - S.G x)) * fun x => ENNReal.ofReal (S.h x)) x
      = S.Ages.indicator (fun x => ENNReal.ofReal (S.g x)) x := by
    intro x hx
    classical
    simp only [Pi.mul_apply]
    rw [Set.indicator_apply]
    split_ifs with hA
    · have hpos : 0 < 1 - S.G x := by linarith [G_lt_one_of_mem S hA]
      rw [← ENNReal.ofReal_mul hpos.le]
      congr 1; simp only [ServiceLaw.h]; field_simp
    · rw [G_eq_one S hx hA]; simp
  rw [setLIntegral_congr_fun measurableSet_Ici e, lintegral_indicator (ages_meas S),
    Measure.restrict_restrict (ages_meas S)]
  -- the complement part vanishes
  have hB : ∫⁻ x in Ici 0 \ S.Ages, ENNReal.ofReal (S.g x) = 0 := by
    by_cases hM : S.M = ⊤
    · have : Ici (0:ℝ) \ S.Ages = ∅ := by
        ext x; simp [ServiceLaw.Ages, hM]
      rw [this]; simp
    · set x0 := S.M.toReal
      have hx0 : 0 ≤ x0 := ENNReal.toReal_nonneg
      have hBset : Ici (0:ℝ) \ S.Ages = Ici x0 := by
        ext x
        simp only [Set.mem_sdiff, mem_Ici]
        constructor
        · rintro ⟨hx, h⟩
          have : ¬ ENNReal.ofReal x < S.M := fun h' => h ⟨hx, h'⟩
          exact (ENNReal.le_ofReal_iff_toReal_le hM hx).mp (not_lt.mp this)
        · intro hx
          refine ⟨le_trans hx0 hx, fun hx' => ?_⟩
          exact absurd hx'.2 (not_lt.mpr ((ENNReal.le_ofReal_iff_toReal_le hM hx'.1).mpr hx))
      have hG : S.G x0 = 1 := by
        apply G_eq_one S hx0
        intro hA
        have : x0 ∈ Ici (0:ℝ) \ S.Ages := by rw [hBset]; exact (le_refl x0 : x0 ≤ x0)
        exact this.2 hA
      rw [hBset, setLIntegral_congr Ioi_ae_eq_Ici.symm,
        ← ofReal_integral_eq_lintegral_ofReal (intOn S _)
          (Eventually.of_forall fun y => S.g_nonneg y), ← one_sub_G, hG]
      simp
  have htot : ∫⁻ x in Ici 0, ENNReal.ofReal (S.g x) = 1 := by
    rw [setLIntegral_congr Ioi_ae_eq_Ici.symm,
      ← ofReal_integral_eq_lintegral_ofReal (intOn S _)
        (Eventually.of_forall fun y => S.g_nonneg y), ← one_sub_G, G_zero]
    simp
  have hsplit := lintegral_inter_add_sdiff (μ := volume)
    (fun x => ENNReal.ofReal (S.g x)) (Ici 0) (ages_meas S)
  rw [Set.inter_comm, ← htot, ← hsplit, hB, add_zero]


lemma stieltjes_max : ManyServerFluid.Uniqueness.stieltjes (fun t : ℝ => max t 0) =
    volume.restrict (Ici 0) := by
  have hmono : Monotone (fun t : ℝ => max (max t 0) 0) := fun a b h => by
    simp only [max_eq_left (le_max_right _ _)]; exact max_le_max h le_rfl
  have hrc : ∀ t, ContinuousWithinAt (fun t : ℝ => max (max t 0) 0) (Ici t) t :=
    fun t => (by fun_prop : Continuous (fun t : ℝ => max (max t 0) 0)).continuousWithinAt
  simp only [ManyServerFluid.Uniqueness.stieltjes]
  rw [dif_pos ⟨hmono, hrc⟩]
  symm
  apply Measure.ext_of_Ioc
  intro a b hab
  rw [StieltjesFunction.measure_Ioc, Measure.restrict_apply measurableSet_Ioc]
  simp only [max_eq_left (le_max_right _ (0:ℝ))]
  rcases le_or_gt 0 a with ha | ha
  · have hs : Ioc a b ∩ Ici 0 = Ioc a b := by
      ext x; simp only [mem_inter_iff, mem_Ioc, mem_Ici]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, by linarith [h.1]⟩
    rw [hs, Real.volume_Ioc,
      max_eq_left ha, max_eq_left (le_trans ha hab.le)]
  · rcases le_or_gt 0 b with hb | hb
    · have : Ioc a b ∩ Ici 0 = Icc 0 b := by
        ext x; simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
        constructor
        · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩
      rw [this, Real.volume_Icc, max_eq_left hb, max_eq_right ha.le, sub_zero]
    · have : Ioc a b ∩ Ici 0 = ∅ := by
        ext x; simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, h2⟩, h3⟩; linarith
      rw [this, max_eq_right hb.le, max_eq_right ha.le]; simp

end R38


open MeasureTheory Filter Topology Set

namespace R38
open ManyServerFluid.Equilibrium

lemma cadlag_of_contOn (f : ℝ → ℝ) (h : ContinuousOn f (Ici 0)) : IsCadlag f :=
  ⟨fun t ht => (h t ht).mono (Ici_subset_Ici.mpr ht),
   fun t ht => ⟨f t, ((h t ht.le).continuousAt (Ici_mem_nhds ht)).tendsto.mono_left
     nhdsWithin_le_nhds⟩⟩

lemma extend (F : ℝ × ℝ → ℝ) (R : Set (ℝ × ℝ)) (hR : IsCompact R) (hF : ContinuousOn F R) :
    ∃ G : ℝ × ℝ → ℝ, Continuous G ∧ (∀ p ∈ R, G p = F p) ∧ ∃ C, ∀ p, |G p| ≤ C := by
  obtain ⟨C0, hC0⟩ := hR.exists_bound_of_continuousOn hF
  set C := max C0 0
  let f : C(R, ℝ) := ⟨R.restrict F, hF.restrict⟩
  obtain ⟨G, hGt, hGr⟩ := ContinuousMap.exists_restrict_eq_forall_mem_of_closed f
    (t := Icc (-C) C) (fun x => by
      have := hC0 x.1 x.2
      rw [Real.norm_eq_abs] at this
      exact abs_le.mp (this.trans (le_max_left _ _)))
    ⟨0, by simp [C]⟩ hR.isClosed
  refine ⟨G, G.continuous, fun p hp => ?_, C, fun p => abs_le.mpr (hGt p)⟩
  have := congrArg (fun F' : C(R, ℝ) => F' ⟨p, hp⟩) hGr
  exact this


/-- the age equation for the constant measure ν* -/
lemma age_nuStar (S : ServiceLaw) (φ Dφ : ℝ × ℝ → ℝ) (hT : S.IsTestFn φ Dφ) (t : ℝ) (ht : 0 ≤ t) :
    ∫ x in Ici 0, (1 - S.G x) * φ (x, t) =
      (∫ x in Ici 0, (1 - S.G x) * φ (x, 0))
      + (∫ s in Icc 0 t, ∫ x in Ici 0, (1 - S.G x) * Dφ (x, s))
      - (∫ s in Icc 0 t, ∫ x in Ici 0, (1 - S.G x) * (S.h x * φ (x, s)))
      + ∫ s in Icc 0 t, φ (0, s) := by
  obtain ⟨hφc, hDc, ⟨m, T, hmM, hsupp⟩, hder⟩ := hT
  set A := S.Ages ×ˢ Ici (0:ℝ)
  -- choose m0 < m1 < b with [0, b] ⊆ Ages
  set m0 := max m 0
  have hm0M : ENNReal.ofReal m0 < S.M := by
    rcases le_or_gt 0 m with hm | hm
    · rwa [show m0 = m from max_eq_left hm]
    · rw [show m0 = 0 from max_eq_right hm.le]
      rw [ENNReal.ofReal_zero]; exact lt_of_le_of_lt bot_le hmM
  obtain ⟨b, hb0, hm0b, hbM⟩ := ENNReal.lt_iff_exists_real_btwn.mp hm0M
  have hm0b' : m0 < b := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_max_right _ _)).mp hm0b
  set m1 := (m0 + b) / 2
  have hm0m1 : m0 < m1 := by simp only [m1]; linarith
  have hm1b : m1 < b := by simp only [m1]; linarith
  have hm1 : 0 ≤ m1 := le_trans (le_max_right _ _) hm0m1.le
  have hmm1 : m < m1 := lt_of_le_of_lt (le_max_left _ _) hm0m1
  have hIccAges : Icc 0 b ⊆ S.Ages := fun x hx =>
    ⟨hx.1, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hx.2) hbM⟩
  set τ := t + 1
  set R := Icc (0:ℝ) b ×ˢ Icc (0:ℝ) τ
  have hRA : R ⊆ A := fun p hp => ⟨hIccAges hp.1, hp.2.1⟩
  have hRc : IsCompact R := isCompact_Icc.prod isCompact_Icc
  obtain ⟨Φ, hΦ, hΦeq, Cφ, hCφ⟩ := extend φ R hRc (hφc.mono hRA)
  obtain ⟨DΦ, hDΦ, hDΦeq, CD, hCD⟩ := extend Dφ R hRc (hDc.mono hRA)
  set C := max Cφ CD
  have hD : ∀ x s, 0 ≤ x → x < b → 0 ≤ s → s < τ →
      Tendsto (fun ε => (Φ (x + ε, s + ε) - Φ (x, s)) / ε) (𝓝[>] 0) (𝓝 (DΦ (x, s))) := by
    intro x s hx hxb hs hsτ
    have hpR : (x, s) ∈ R := ⟨⟨hx, hxb.le⟩, ⟨hs, hsτ.le⟩⟩
    rw [hDΦeq _ hpR]
    have h := hder (x, s) (hRA hpR)
    refine h.congr' ?_
    have hpos : 0 < min (b - x) (τ - s) := lt_min (by linarith) (by linarith)
    filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
    have hq : (x + ε, s + ε) ∈ R :=
      ⟨⟨by linarith [hε.1], by linarith [hε.2, min_le_left (b - x) (τ - s)]⟩,
       ⟨by linarith [hε.1], by linarith [hε.2, min_le_right (b - x) (τ - s)]⟩⟩
    rw [hΦeq _ hq, hΦeq _ hpR]
  have hzero : ∀ s, 0 ≤ s → s ≤ t → Φ (m1, s) = 0 := by
    intro s hs hst
    have hp : (m1, s) ∈ R := ⟨⟨hm1, hm1b.le⟩, ⟨hs, by simp only [τ]; linarith⟩⟩
    rw [hΦeq _ hp]
    exact (hsupp _ (hRA hp) (Or.inl hmm1)).1
  have hW := core_W Φ DΦ hΦ hDΦ b τ hD C (fun p => (hCφ p).trans (le_max_left _ _))
    (fun p => (hCD p).trans (le_max_right _ _)) S.g S.measurable_g S.integrable_g S.g_nonneg
    S.g_eq_zero_of_neg S.integral_g hm1 hm1b ht (by simp only [τ]; linarith) hzero
  -- transfers
  have hsub1 : Icc 0 m1 ⊆ S.Ages := fun x hx => hIccAges ⟨hx.1, hx.2.trans hm1b.le⟩
  have tr : ∀ (F G : ℝ × ℝ → ℝ), (∀ p ∈ R, G p = F p) → (∀ p ∈ A, m < p.1 → F p = 0) →
      ∀ s, 0 ≤ s → s ≤ t →
      ∫ x in Ici 0, (1 - S.G x) * F (x, s) = ∫ x in (0:ℝ)..m1, G (x, s) * ∫ y in Ioi x, S.g y := by
    intro F G hGF hF0 s hs hst
    apply transfer S (fun x => F (x, s)) (fun x => G (x, s)) hm1 hsub1
    · intro x hx hxm
      exact (hGF (x, s) ⟨⟨hx.1, hxm.trans hm1b.le⟩, ⟨hs, by simp only [τ]; linarith⟩⟩).symm
    · intro x hx hxm
      exact hF0 (x, s) ⟨hx, hs⟩ (lt_trans hmm1 hxm)
  have trh : ∀ s, 0 ≤ s → s ≤ t →
      ∫ x in Ici 0, (1 - S.G x) * (S.h x * φ (x, s)) = ∫ x in (0:ℝ)..m1, S.g x * Φ (x, s) := by
    intro s hs hst
    apply transfer_h S (fun x => φ (x, s)) (fun x => Φ (x, s)) hm1 hsub1
    · intro x hx hxm
      exact (hΦeq (x, s) ⟨⟨hx.1, hxm.trans hm1b.le⟩, ⟨hs, by simp only [τ]; linarith⟩⟩).symm
    · intro x hx hxm
      exact (hsupp (x, s) ⟨hx, hs⟩ (Or.inl (lt_trans hmm1 hxm))).1
  have hφ0 : ∀ p ∈ A, m < p.1 → φ p = 0 := fun p hp h => (hsupp p hp (Or.inl h)).1
  have hD0 : ∀ p ∈ A, m < p.1 → Dφ p = 0 := fun p hp h => (hsupp p hp (Or.inl h)).2
  have et : ∫ x in Ici 0, (1 - S.G x) * φ (x, t) =
      ∫ x in (0:ℝ)..m1, Φ (x, t) * ∫ y in Ioi x, S.g y := tr φ Φ hΦeq hφ0 t ht le_rfl
  have e0 : ∫ x in Ici 0, (1 - S.G x) * φ (x, 0) =
      ∫ x in (0:ℝ)..m1, Φ (x, 0) * ∫ y in Ioi x, S.g y := tr φ Φ hΦeq hφ0 0 le_rfl ht
  rw [et, e0]
  have e1 : ∫ s in Icc 0 t, ∫ x in Ici 0, (1 - S.G x) * Dφ (x, s) =
      ∫ s in (0:ℝ)..t, ∫ x in (0:ℝ)..m1, DΦ (x, s) * ∫ y in Ioi x, S.g y := by
    rw [intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc]
    exact setIntegral_congr_fun measurableSet_Icc fun s hs => tr Dφ DΦ hDΦeq hD0 s hs.1 hs.2
  have e2 : ∫ s in Icc 0 t, ∫ x in Ici 0, (1 - S.G x) * (S.h x * φ (x, s)) =
      ∫ s in (0:ℝ)..t, ∫ x in (0:ℝ)..m1, S.g x * Φ (x, s) := by
    rw [intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc]
    exact setIntegral_congr_fun measurableSet_Icc fun s hs => trh s hs.1 hs.2
  have e3 : ∫ s in Icc 0 t, φ (0, s) = ∫ s in (0:ℝ)..t, Φ (0, s) := by
    rw [intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    exact (hΦeq (0, s) ⟨⟨le_rfl, hb0⟩, ⟨hs.1, by simp only [τ]; linarith [hs.2]⟩⟩).symm
  rw [e1, e2, e3, hW]

end R38

namespace R38
open ManyServerFluid.Equilibrium

lemma kbar_const (S : ServiceLaw) (νstar : FiniteMeasure ℝ)
    (hνstar : (νstar : Measure ℝ) = S.nuStar) :
    S.Kbar (fun _ => νstar) = fun t => max t 0 := by
  have hInt : ∀ t, S.hInt (fun _ => νstar) t = ENNReal.ofReal t := by
    intro t
    simp only [ServiceLaw.hInt]
    rw [hνstar, R38.lint_h, setLIntegral_const, one_mul, Real.volume_Icc, sub_zero]
  funext t
  simp only [ServiceLaw.Kbar, ServiceLaw.Dbar, hInt, ENNReal.toReal_ofReal', sub_self, zero_add]

end R38


open MeasureTheory Filter Topology Set

namespace R38
open ManyServerFluid.Equilibrium

noncomputable def gU : ℝ → ℝ := (Icc (0:ℝ) 2).indicator fun _ => (1/2 : ℝ)

lemma gU_meas : Measurable gU := measurable_const.indicator measurableSet_Icc

lemma gU_int : Integrable gU :=
  (integrableOn_const (C := (1/2:ℝ)) (by simp)).integrable_indicator measurableSet_Icc

lemma gU_integral : ∫ x, gU x = 1 := by
  rw [gU, integral_indicator measurableSet_Icc, setIntegral_const]
  norm_num

lemma gU_mean_eq : (fun x => x * gU x) = (Icc (0:ℝ) 2).indicator fun x => x * (1/2) := by
  ext x; simp only [gU, Set.indicator_apply]; split_ifs <;> simp

lemma gU_mean_int : Integrable fun x => x * gU x := by
  rw [gU_mean_eq]
  exact ((continuous_id.mul continuous_const).integrableOn_Icc).integrable_indicator
    measurableSet_Icc

lemma gU_mean : ∫ x, x * gU x = 1 := by
  rw [gU_mean_eq, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_mul_const,
    integral_id]
  norm_num

noncomputable def SU : ServiceLaw where
  g := gU
  measurable_g := gU_meas
  g_nonneg := fun x => by
    simp only [gU, Set.indicator_apply]; split_ifs <;> norm_num
  g_eq_zero_of_neg := fun x hx => by
    simp only [gU, Set.indicator_apply, mem_Icc]
    rw [if_neg (by intro h; linarith [h.1])]
  integrable_g := gU_int
  integral_g := gU_integral
  integrable_mean := gU_mean_int
  mean_one := gU_mean

lemma SU_G_one : SU.G 1 = 1 / 2 := by
  simp only [ServiceLaw.G, SU, gU]
  rw [setIntegral_indicator measurableSet_Icc, setIntegral_const]
  have : Iic (1:ℝ) ∩ Icc 0 2 = Icc 0 1 := by
    ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
  rw [this]; simp [Real.volume_Icc]

lemma SU_one_mem : (1:ℝ) ∈ SU.Ages :=
  mem_of_G_lt_one SU zero_le_one (by rw [SU_G_one]; norm_num)



lemma st_hasDeriv (y : ℝ) : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition y) y :=
  ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)).differentiableAt.hasDerivAt

lemma dst_cont : Continuous (deriv Real.smoothTransition) :=
  (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl

lemma dst_neg {y : ℝ} (hy : y < 0) : deriv Real.smoothTransition y = 0 := by
  have : Real.smoothTransition =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds hy] with z hz
    exact Real.smoothTransition.zero_of_nonpos hz.le
  rw [this.deriv_eq]; simp

lemma dst_gt {y : ℝ} (hy : 1 < y) : deriv Real.smoothTransition y = 0 := by
  have : Real.smoothTransition =ᶠ[𝓝 y] fun _ => 1 := by
    filter_upwards [Ioi_mem_nhds hy] with z hz
    exact Real.smoothTransition.one_of_one_le hz.le
  rw [this.deriv_eq]; simp

lemma dst_bdd : ∃ C, ∀ y, |deriv Real.smoothTransition y| ≤ C := by
  have hcs : HasCompactSupport (deriv Real.smoothTransition) := by
    apply HasCompactSupport.intro (isCompact_Icc (a := (0:ℝ)) (b := 1))
    intro y hy
    simp only [mem_Icc, not_and_or, not_le] at hy
    rcases hy with hy | hy
    · exact dst_neg hy
    · exact dst_gt hy
  obtain ⟨C, hC⟩ := dst_cont.bounded_above_of_compact_support hcs
  exact ⟨C, fun y => by simpa using hC y⟩

noncomputable def φt (p : ℝ × ℝ) : ℝ := Real.smoothTransition (1 - p.1) * Real.smoothTransition (2 - p.2)
noncomputable def Dφt (p : ℝ × ℝ) : ℝ :=
  -(deriv Real.smoothTransition (1 - p.1)) * Real.smoothTransition (2 - p.2) - Real.smoothTransition (1 - p.1) * deriv Real.smoothTransition (2 - p.2)

lemma φt_cont : Continuous φt := by
  unfold φt
  exact (Real.smoothTransition.continuous.comp (by fun_prop)).mul
    (Real.smoothTransition.continuous.comp (by fun_prop))

lemma Dφt_cont : Continuous Dφt := by
  unfold Dφt
  have c1 : Continuous fun p : ℝ × ℝ => Real.smoothTransition (1 - p.1) :=
    Real.smoothTransition.continuous.comp (by fun_prop)
  have c2 : Continuous fun p : ℝ × ℝ => Real.smoothTransition (2 - p.2) :=
    Real.smoothTransition.continuous.comp (by fun_prop)
  have d1 : Continuous fun p : ℝ × ℝ => deriv Real.smoothTransition (1 - p.1) := dst_cont.comp (by fun_prop)
  have d2 : Continuous fun p : ℝ × ℝ => deriv Real.smoothTransition (2 - p.2) := dst_cont.comp (by fun_prop)
  exact (d1.neg.mul c2).sub (c1.mul d2)

lemma φt_test : SU.IsTestFn φt Dφt := by
  refine ⟨φt_cont.continuousOn, Dφt_cont.continuousOn, ⟨1, 2, SU_one_mem.2, ?_⟩, ?_⟩
  · intro p _ hp
    rcases hp with hp | hp
    · have h1 : 1 - p.1 < 0 := by linarith
      simp only [φt, Dφt, Real.smoothTransition.zero_of_nonpos h1.le, dst_neg h1]
      simp
    · have h1 : 2 - p.2 < 0 := by linarith
      simp only [φt, Dφt, Real.smoothTransition.zero_of_nonpos h1.le, dst_neg h1]
      simp
  · intro p _
    have hd1 : HasDerivAt (fun r : ℝ => Real.smoothTransition (1 - (p.1 + r))) (deriv Real.smoothTransition (1 - p.1) * (-1)) 0 := by
      have := (st_hasDeriv (1 - (p.1 + 0))).comp (0:ℝ)
        ((((hasDerivAt_id (0:ℝ)).const_add p.1).const_sub 1))
      simp only [add_zero, id] at this
      exact this
    have hd2 : HasDerivAt (fun r : ℝ => Real.smoothTransition (2 - (p.2 + r))) (deriv Real.smoothTransition (2 - p.2) * (-1)) 0 := by
      have := (st_hasDeriv (2 - (p.2 + 0))).comp (0:ℝ)
        ((((hasDerivAt_id (0:ℝ)).const_add p.2).const_sub 2))
      simp only [add_zero, id] at this
      exact this
    have hq := hd1.mul hd2
    rw [hasDerivAt_iff_tendsto_slope_zero] at hq
    have hq' := hq.mono_left (nhdsWithin_mono _ (fun x (hx : x ∈ Ioi (0:ℝ)) => ne_of_gt hx))
    have heq : deriv Real.smoothTransition (1 - p.1) * -1 * Real.smoothTransition (2 - (p.2 + 0)) + Real.smoothTransition (1 - (p.1 + 0)) *
        (deriv Real.smoothTransition (2 - p.2) * -1) = Dφt p := by
      simp only [Dφt, add_zero]; ring
    rw [heq] at hq'
    refine hq'.congr' ?_
    filter_upwards with ε
    simp only [φt, Pi.mul_apply, zero_add, add_zero, smul_eq_mul, div_eq_inv_mul]


lemma st_abs (y : ℝ) : |Real.smoothTransition y| ≤ 1 := by
  rw [abs_of_nonneg (Real.smoothTransition.nonneg y)]; exact Real.smoothTransition.le_one y

lemma φt_bdd (p : ℝ × ℝ) : |φt p| ≤ 1 := by
  simp only [φt, abs_mul]
  exact mul_le_one₀ (st_abs _) (abs_nonneg _) (st_abs _)

lemma Dφt_bdd : ∃ C, ∀ p, |Dφt p| ≤ C := by
  obtain ⟨C, hC⟩ := dst_bdd
  refine ⟨C + C, fun p => ?_⟩
  simp only [Dφt]
  have h1 : |-(deriv Real.smoothTransition (1 - p.1)) * Real.smoothTransition (2 - p.2)| ≤ C := by
    rw [abs_mul, abs_neg]
    calc |deriv Real.smoothTransition (1 - p.1)| * |Real.smoothTransition (2 - p.2)| ≤ C * 1 :=
          mul_le_mul (hC _) (st_abs _) (abs_nonneg _) (le_trans (abs_nonneg _) (hC 0))
      _ = C := mul_one C
  have h2 : |Real.smoothTransition (1 - p.1) * deriv Real.smoothTransition (2 - p.2)| ≤ C := by
    rw [abs_mul]
    calc |Real.smoothTransition (1 - p.1)| * |deriv Real.smoothTransition (2 - p.2)| ≤ 1 * C :=
          mul_le_mul (st_abs _) (hC _) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  exact (abs_sub _ _).trans (add_le_add h1 h2)

lemma h_nonneg (S : ServiceLaw) (x : ℝ) : 0 ≤ S.h x :=
  div_nonneg (S.g_nonneg x) (by linarith [G_le_one S x])

lemma h_int (S : ServiceLaw) : Integrable S.h S.nuStar := by
  refine ⟨(h_meas S).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have : ∀ x, ‖S.h x‖ₑ = ENNReal.ofReal (S.h x) := fun x => by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (h_nonneg S x)]
  simp_rw [this]
  rw [lint_h]; exact ENNReal.one_lt_top

instance (S : ServiceLaw) : IsFiniteMeasure S.nuStar := ⟨by rw [nuStar_univ]; exact ENNReal.one_lt_top⟩

end R38

open ManyServerFluid.Equilibrium R38 in
theorem solution : ¬ (∀ (S : ServiceLaw) (lam E : ℝ → ℝ) (c : ℝ) (νstar : FiniteMeasure ℝ),
    (νstar : Measure ℝ) = S.nuStar →
    (∀ t, IntegrableOn lam (Icc 0 t)) →
    (∀ t, 0 ≤ t → E t = ∫ s in Icc 0 t, lam s) →
    (∀ᵐ s ∂(volume.restrict (Ici (0 : ℝ))), 1 ≤ lam s) →
    1 ≤ c →
    S.InS0 E c νstar ∧
    S.IsFluidSolution E c νstar (fun t => c + E t - t) (fun _ => νstar) ∧
    ∀ t, 0 ≤ t → S.Kbar (fun _ => νstar) t = t) := by
  intro H
  let ν : FiniteMeasure ℝ := ⟨SU.nuStar, inferInstance⟩
  have hν : (ν : Measure ℝ) = SU.nuStar := rfl
  obtain ⟨-, hsol, -⟩ := H SU (fun _ => 1) (fun t => ∫ s in Icc 0 t, (1:ℝ)) 1 ν hν
    (fun t => integrableOn_const (by simp)) (fun t _ => rfl)
    (Eventually.of_forall fun _ => le_rfl) le_rfl
  have hage := hsol.age φt Dφt φt_test 1 zero_le_one
  rw [kbar_const SU ν hν, stieltjes_max, Measure.restrict_restrict measurableSet_Icc,
    inter_eq_left.mpr (Icc_subset_Ici_self : Icc (0:ℝ) 1 ⊆ Ici 0)] at hage
  simp only [hν] at hage
  -- continuity of the two time integrands
  obtain ⟨CD, hCD⟩ := Dφt_bdd
  have ha : Continuous fun s => ∫ x, Dφt (x, s) ∂SU.nuStar := by
    apply continuous_of_dominated (bound := fun _ => CD)
    · exact fun s => (Dφt_cont.comp (by fun_prop)).aestronglyMeasurable
    · exact fun s => Eventually.of_forall fun x => by simpa using hCD (x, s)
    · exact integrable_const _
    · exact Eventually.of_forall fun x => Dφt_cont.comp (by fun_prop)
  have hb : Continuous fun s => ∫ x, SU.h x * φt (x, s) ∂SU.nuStar := by
    apply continuous_of_dominated (bound := fun x => |SU.h x|)
    · exact fun s => ((h_meas SU).mul (φt_cont.comp (by fun_prop)).measurable).aestronglyMeasurable
    · refine fun s => Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (φt_bdd _)
    · exact (h_int SU).abs
    · exact Eventually.of_forall fun x => continuous_const.mul (φt_cont.comp (by fun_prop))
  have hC1 : ∫ s in Icc (0:ℝ) 1, φt (0, s) = 1 := by
    rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => (1:ℝ))]
    · simp
    · intro s hs
      simp only [φt, sub_zero, Real.smoothTransition.one,
        Real.smoothTransition.one_of_one_le (show (1:ℝ) ≤ 2 - s by linarith [hs.2]), mul_one]
  rw [hC1] at hage
  have i1 := integral_sub (μ := volume.restrict (Icc (0:ℝ) 1)) (ha.integrableOn_Icc)
    (integrable_const (∫ s' in Icc (0:ℝ) 1, ((∫ x, SU.h x * φt (x, s') ∂SU.nuStar) + 1)))
  have i2 := integral_add (μ := volume.restrict (Icc (0:ℝ) 1)) (hb.integrableOn_Icc)
    (integrable_const (1:ℝ))
  simp only [setIntegral_const, Real.volume_real_Icc, sub_zero, max_eq_left zero_le_one,
    one_smul] at i1 i2
  rw [i1, i2] at hage
  have htrue := age_nuStar SU φt Dφt φt_test 1 zero_le_one
  simp only [← nuStar_integral] at htrue
  rw [hC1] at htrue
  linarith



