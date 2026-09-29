-- Prove2me | solution 1 for MeasureTheory.differentiable_and_continuous_integral_mul_cpow_of_eventually_norm_mul_rpow_add_rpow_neg_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/180755b3-0940-5ba1-9930-9989f92d604b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_differentiable_and_continuous_integral_mul_cpow_of_eventually_norm_mul_rpow_add_rpow_neg_le

set_option autoImplicit false

noncomputable section

open MeasureTheory Complex Filter Topology Real

namespace ParametricMellin

theorem rpow_le_rpow_add_rpow_neg {y : ℝ} (hy : 0 < y) {t M : ℝ} (ht : |t| ≤ M) :
    y ^ t ≤ y ^ M + y ^ (-M) := by
  have h1 : t ≤ M := (le_abs_self t).trans ht
  have h2 : -M ≤ t := by have := neg_abs_le t; linarith
  rcases le_or_gt 1 y with h | h
  · exact le_add_of_le_of_nonneg (Real.rpow_le_rpow_of_exponent_le h h1) (Real.rpow_nonneg hy.le _)
  · exact le_add_of_nonneg_of_le (Real.rpow_nonneg hy.le _)
      (Real.rpow_le_rpow_of_exponent_ge hy h.le h2)

theorem abs_log_le_add_inv {y : ℝ} (hy : 0 < y) : |Real.log y| ≤ y + y⁻¹ := by
  rw [abs_le]
  constructor
  · have h := Real.log_le_sub_one_of_pos (inv_pos.2 hy)
    rw [Real.log_inv] at h
    have : 0 ≤ y := hy.le
    linarith
  · have h := Real.log_le_sub_one_of_pos hy
    have : 0 ≤ y⁻¹ := inv_nonneg.2 hy.le
    linarith

theorem rpow_mul_add_inv {y : ℝ} (hy : 0 < y) (t : ℝ) :
    y ^ t * (y + y⁻¹) = y ^ (t + 1) + y ^ (t - 1) := by
  rw [mul_add, Real.rpow_add hy, Real.rpow_one, Real.rpow_sub hy, Real.rpow_one, div_eq_mul_inv]

theorem rpow_mul_abs_log_le {y : ℝ} (hy : 0 < y) {t M : ℝ} (ht : |t| + 1 ≤ M) :
    y ^ t * |Real.log y| ≤ 2 * (y ^ M + y ^ (-M)) := by
  have h0 : 0 ≤ y ^ t := Real.rpow_nonneg hy.le _
  calc y ^ t * |Real.log y| ≤ y ^ t * (y + y⁻¹) :=
        mul_le_mul_of_nonneg_left (abs_log_le_add_inv hy) h0
    _ = y ^ (t + 1) + y ^ (t - 1) := rpow_mul_add_inv hy t
    _ ≤ (y ^ M + y ^ (-M)) + (y ^ M + y ^ (-M)) := by
        refine add_le_add (rpow_le_rpow_add_rpow_neg hy ?_) (rpow_le_rpow_add_rpow_neg hy ?_)
        · calc |t + 1| ≤ |t| + |1| := abs_add_le _ _
            _ = |t| + 1 := by rw [abs_one]
            _ ≤ M := ht
        · calc |t - 1| ≤ |t| + |1| := abs_sub _ _
            _ = |t| + 1 := by rw [abs_one]
            _ ≤ M := ht
    _ = 2 * (y ^ M + y ^ (-M)) := by ring

variable {X : Type*} [MeasurableSpace X] (m : Measure X) (N : X → ℝ)

omit [MeasurableSpace X] in
theorem norm_mul_cpow {x : X} (hx : 0 < N x) (c : ℂ) (s : ℂ) :
    ‖c * ((N x : ℝ) : ℂ) ^ s‖ = ‖c‖ * N x ^ s.re := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]

theorem aestronglyMeasurable_cpow (hN : AEMeasurable N m) (c : ℂ) :
    AEStronglyMeasurable (fun x => ((N x : ℝ) : ℂ) ^ c) m :=
  ((Complex.measurable_ofReal.comp_aemeasurable hN).pow_const c).aestronglyMeasurable

theorem aestronglyMeasurable_integrand {g : X → ℂ} (hg : AEStronglyMeasurable g m) (hN : AEMeasurable N m)
    (s : ℂ) : AEStronglyMeasurable (fun x => g x * ((N x : ℝ) : ℂ) ^ s) m :=
  hg.mul (aestronglyMeasurable_cpow m N hN _)

theorem aestronglyMeasurable_deriv_integrand {g : X → ℂ} (hg : AEStronglyMeasurable g m) (hN : AEMeasurable N m)
    (s : ℂ) :
    AEStronglyMeasurable (fun x => g x * (((N x : ℝ) : ℂ) ^ s * ((Real.log (N x) : ℝ) : ℂ))) m := by
  refine hg.mul ((aestronglyMeasurable_cpow m N hN _).mul ?_)
  exact (Complex.measurable_ofReal.comp_aemeasurable
    (Real.measurable_log.comp_aemeasurable hN)).aestronglyMeasurable

theorem aestronglyMeasurable_majorant {g : X → ℂ} (hg : AEStronglyMeasurable g m) (hN : AEMeasurable N m)
    (M : ℝ) : AEStronglyMeasurable (fun x => ‖g x‖ * (N x ^ M + N x ^ (-M))) m := by
  refine (hg.norm.aemeasurable.mul ((hN.pow_const M).add (hN.pow_const (-M)))).aestronglyMeasurable

omit [MeasurableSpace X] in
theorem norm_integrand_le {x : X} (hx : 0 < N x) (c : ℂ) {s : ℂ} {M : ℝ} (hs : |s.re| ≤ M) :
    ‖c * ((N x : ℝ) : ℂ) ^ s‖ ≤ ‖c‖ * (N x ^ M + N x ^ (-M)) := by
  rw [norm_mul_cpow N hx]
  exact mul_le_mul_of_nonneg_left (rpow_le_rpow_add_rpow_neg hx hs) (norm_nonneg _)

omit [MeasurableSpace X] in
theorem norm_deriv_integrand_le {x : X} (hx : 0 < N x) (c : ℂ) {s : ℂ} {M : ℝ} (hs : |s.re| + 1 ≤ M) :
    ‖c * (((N x : ℝ) : ℂ) ^ s * ((Real.log (N x) : ℝ) : ℂ))‖ ≤ 2 * (‖c‖ * (N x ^ M + N x ^ (-M))) := by
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_real, Real.norm_eq_abs]
  have := rpow_mul_abs_log_le hx hs
  calc ‖c‖ * (N x ^ s.re * |Real.log (N x)|)
      ≤ ‖c‖ * (2 * (N x ^ M + N x ^ (-M))) := mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = 2 * (‖c‖ * (N x ^ M + N x ^ (-M))) := by ring

omit [MeasurableSpace X] in
theorem majorant_nonneg {x : X} (hx : 0 < N x) (c : ℂ) (M : ℝ) : 0 ≤ ‖c‖ * (N x ^ M + N x ^ (-M)) :=
  mul_nonneg (norm_nonneg _) (add_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hx.le _))

section OneFunction

variable {m N}
variable (hN : AEMeasurable N m) (hNpos : ∀ x, 0 < N x) {g : X → ℂ} (hg : AEStronglyMeasurable g m)

include hN hNpos hg

theorem integrable_majorant_of_le {M : ℝ} {bound : X → ℝ} (hb : Integrable bound m)
    (hle : ∀ᵐ x ∂m, ‖g x‖ * (N x ^ M + N x ^ (-M)) ≤ bound x) :
    Integrable (fun x => ‖g x‖ * (N x ^ M + N x ^ (-M))) m := by
  refine hb.mono' (aestronglyMeasurable_majorant m N hg hN M) ?_
  filter_upwards [hle] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (majorant_nonneg N (hNpos x) (g x) M)]
  exact hx

theorem integrable_integrand {M : ℝ} (hmom : Integrable (fun x => ‖g x‖ * (N x ^ M + N x ^ (-M))) m)
    {s : ℂ} (hs : |s.re| ≤ M) : Integrable (fun x => g x * ((N x : ℝ) : ℂ) ^ s) m := by
  refine hmom.mono' (aestronglyMeasurable_integrand m N hg hN s) ?_
  exact Filter.Eventually.of_forall fun x => norm_integrand_le N (hNpos x) (g x) hs

omit hN hg in

theorem norm_integral_le {M : ℝ} (hmom : Integrable (fun x => ‖g x‖ * (N x ^ M + N x ^ (-M))) m)
    {s : ℂ} (hs : |s.re| ≤ M) :
    ‖∫ x, g x * ((N x : ℝ) : ℂ) ^ s ∂m‖ ≤ ∫ x, ‖g x‖ * (N x ^ M + N x ^ (-M)) ∂m :=
  norm_integral_le_of_norm_le hmom (Filter.Eventually.of_forall fun x => norm_integrand_le N (hNpos x) (g x) hs)

theorem hasDerivAt_integral {s₀ : ℂ} {M : ℝ} (hM : |s₀.re| + 2 ≤ M)
    (hmom : Integrable (fun x => ‖g x‖ * (N x ^ M + N x ^ (-M))) m) :
    HasDerivAt (fun s : ℂ => ∫ x, g x * ((N x : ℝ) : ℂ) ^ s ∂m)
      (∫ x, g x * (((N x : ℝ) : ℂ) ^ s₀ * ((Real.log (N x) : ℝ) : ℂ)) ∂m) s₀ := by
  set F : ℂ → X → ℂ := fun s x => g x * ((N x : ℝ) : ℂ) ^ s with hF
  set F' : ℂ → X → ℂ := fun s x => g x * (((N x : ℝ) : ℂ) ^ s * ((Real.log (N x) : ℝ) : ℂ)) with hF'
  set bound : X → ℝ := fun x => 2 * (‖g x‖ * (N x ^ M + N x ^ (-M))) with hbound
  have hball : Metric.ball s₀ 1 ∈ 𝓝 s₀ := Metric.ball_mem_nhds _ one_pos
  have h1 : ∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable (F s) m :=
    Filter.Eventually.of_forall fun s => aestronglyMeasurable_integrand m N hg hN s
  have h2 : Integrable (F s₀) m := integrable_integrand hN hNpos hg hmom (by linarith)
  have h3 : AEStronglyMeasurable (F' s₀) m := aestronglyMeasurable_deriv_integrand m N hg hN s₀
  have hstrip : ∀ s ∈ Metric.ball s₀ 1, |s.re| + 1 ≤ M := by
    intro s hs
    rw [Metric.mem_ball, dist_eq_norm] at hs
    have hre : |s.re - s₀.re| < 1 := by
      have := abs_re_le_norm (s - s₀)
      rw [sub_re] at this
      exact lt_of_le_of_lt this hs
    have : |s.re| ≤ |s₀.re| + 1 := by
      calc |s.re| = |(s.re - s₀.re) + s₀.re| := by ring_nf
        _ ≤ |s.re - s₀.re| + |s₀.re| := abs_add_le _ _
        _ ≤ 1 + |s₀.re| := by linarith [hre.le]
        _ = |s₀.re| + 1 := by ring
    linarith
  have h4 : ∀ᵐ x ∂m, ∀ s ∈ Metric.ball s₀ 1, ‖F' s x‖ ≤ bound x :=
    Filter.Eventually.of_forall fun x s hs => norm_deriv_integrand_le N (hNpos x) (g x) (hstrip s hs)
  have h5 : Integrable bound m := hmom.const_mul 2
  have h6 : ∀ᵐ x ∂m, ∀ s ∈ Metric.ball s₀ 1, HasDerivAt (fun z => F z x) (F' s x) s := by
    refine Filter.Eventually.of_forall fun x s _ => ?_
    have hx : ((N x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hNpos x).ne'
    have u : HasDerivAt (fun z : ℂ => ((N x : ℝ) : ℂ) ^ z)
        (((N x : ℝ) : ℂ) ^ s * Complex.log ((N x : ℝ) : ℂ) * 1) s :=
      (hasDerivAt_id s).const_cpow (Or.inl hx)
    rw [mul_one, ← Complex.ofReal_log (hNpos x).le] at u
    exact u.const_mul (g x)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hball h1 h2 h3 h4 h5 h6).2

end OneFunction

theorem main
    {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    (hN : AEMeasurable N m) (hNpos : ∀ x, 0 < N x)
    (h : P → X → ℂ) (hh : ∀ p, AEStronglyMeasurable (h p) m)
    (hcont : ∀ᵐ x ∂m, Continuous fun p => h p x)
    (hdom : ∀ (p₀ : P) (M : ℝ), ∃ bound : X → ℝ, Integrable bound m ∧
      ∀ᶠ p in nhds p₀, ∀ᵐ x ∂m, ‖h p x‖ * (N x ^ M + N x ^ (-M)) ≤ bound x) :
    (∀ p : P, Differentiable ℂ fun s : ℂ => ∫ x, h p x * ((N x : ℝ) : ℂ) ^ s ∂m) ∧
    (Continuous fun q : ℂ × P => ∫ x, h q.2 x * ((N x : ℝ) : ℂ) ^ q.1 ∂m) ∧
    (∀ (p : P) (M : ℝ) (s : ℂ), |s.re| ≤ M →
      Integrable (fun x => ‖h p x‖ * (N x ^ M + N x ^ (-M))) m ∧
      ‖∫ x, h p x * ((N x : ℝ) : ℂ) ^ s ∂m‖ ≤ ∫ x, ‖h p x‖ * (N x ^ M + N x ^ (-M)) ∂m) := by

  have hmomAt : ∀ (p : P) (M : ℝ), Integrable (fun x => ‖h p x‖ * (N x ^ M + N x ^ (-M))) m := by
    intro p M
    obtain ⟨bound, hb, hev⟩ := hdom p M
    exact integrable_majorant_of_le hN hNpos (hh p) hb hev.self_of_nhds
  refine ⟨fun p s₀ => ?_, ?_, fun p M s hs => ⟨hmomAt p M, norm_integral_le hNpos (hmomAt p M) hs⟩⟩
  ·
    exact (hasDerivAt_integral hN hNpos (hh p) (le_refl (|s₀.re| + 2)) (hmomAt p (|s₀.re| + 2))).differentiableAt
  ·
    refine continuous_iff_continuousAt.2 fun q₀ => ?_
    obtain ⟨s₀, p₀⟩ := q₀
    set M : ℝ := |s₀.re| + 1 with hM
    obtain ⟨bound, hb, hev⟩ := hdom p₀ M

    have hS : {s : ℂ | |s.re| ≤ M} ∈ 𝓝 s₀ := by
      have hopen : IsOpen {s : ℂ | |s.re - s₀.re| < 1} :=
        isOpen_lt (continuous_abs.comp (Complex.continuous_re.sub continuous_const)) continuous_const
      refine Filter.mem_of_superset (hopen.mem_nhds (by simp)) fun s hs => ?_
      simp only [Set.mem_setOf_eq] at hs ⊢
      calc |s.re| = |(s.re - s₀.re) + s₀.re| := by ring_nf
        _ ≤ |s.re - s₀.re| + |s₀.re| := abs_add_le _ _
        _ ≤ M := by rw [hM]; linarith [hs.le]
    have hprod : ∀ᶠ q : ℂ × P in 𝓝 (s₀, p₀), |q.1.re| ≤ M ∧
        ∀ᵐ x ∂m, ‖h q.2 x‖ * (N x ^ M + N x ^ (-M)) ≤ bound x := by
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod hS hev
    refine continuousAt_of_dominated (bound := bound) ?_ ?_ hb ?_
    · exact Filter.Eventually.of_forall fun q => aestronglyMeasurable_integrand m N (hh q.2) hN q.1
    · filter_upwards [hprod] with q hq
      filter_upwards [hq.2] with x hx
      exact (norm_integrand_le N (hNpos x) (h q.2 x) hq.1).trans hx
    · filter_upwards [hcont] with x hx
      have hxN : ((N x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hNpos x).ne'
      have hc1 : Continuous fun q : ℂ × P => h q.2 x := hx.comp continuous_snd
      have hc2 : Continuous fun q : ℂ × P => ((N x : ℝ) : ℂ) ^ q.1 :=
        (@continuous_const_cpow ((N x : ℝ) : ℂ) ⟨hxN⟩).comp continuous_fst
      exact (hc1.mul hc2).continuousAt

end ParametricMellin

theorem solution
    {X : Type*} [MeasurableSpace X] (m : MeasureTheory.Measure X)
    {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    (N : X → ℝ) (hN : AEMeasurable N m) (hNpos : ∀ x, 0 < N x)
    (h : P → X → ℂ) (hh : ∀ p, MeasureTheory.AEStronglyMeasurable (h p) m)
    (hcont : ∀ᵐ x ∂m, Continuous fun p => h p x)
    (hdom : ∀ (p₀ : P) (M : ℝ), ∃ bound : X → ℝ, MeasureTheory.Integrable bound m ∧
      ∀ᶠ p in nhds p₀, ∀ᵐ x ∂m, ‖h p x‖ * (N x ^ M + N x ^ (-M)) ≤ bound x) :
    (∀ p : P, Differentiable ℂ fun s : ℂ => ∫ x, h p x * ((N x : ℝ) : ℂ) ^ s ∂m) ∧
    (Continuous fun q : ℂ × P => ∫ x, h q.2 x * ((N x : ℝ) : ℂ) ^ q.1 ∂m) ∧
    (∀ (p : P) (M : ℝ) (s : ℂ), |s.re| ≤ M →
      MeasureTheory.Integrable (fun x => ‖h p x‖ * (N x ^ M + N x ^ (-M))) m ∧
      ‖∫ x, h p x * ((N x : ℝ) : ℂ) ^ s ∂m‖ ≤ ∫ x, ‖h p x‖ * (N x ^ M + N x ^ (-M)) ∂m) :=
  ParametricMellin.main m N hN hNpos h hh hcont hdom

end

end S_MeasureTheory_differentiable_and_continuous_integral_mul_cpow_of_eventually_norm_mul_rpow_add_rpow_neg_le
end P2MW
export P2MW.S_MeasureTheory_differentiable_and_continuous_integral_mul_cpow_of_eventually_norm_mul_rpow_add_rpow_neg_le (solution)
