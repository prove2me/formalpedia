-- Prove2me | solution 1 for LanglandsTunnell.eq_zero_of_mellin_eq_GammaC_mul_of_sub_rpow_bound_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e7340296-ff06-5fe3-ae08-b861521bebff

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_eq_zero_of_mellin_eq_GammaC_mul_of_sub_rpow_bound_near_zero

set_option autoImplicit false

noncomputable section

open Real Complex Filter Topology MeasureTheory Set Asymptotics

namespace LanglandsTunnell
namespace PoleClash

theorem abs_log_le_rpow_add (t v : ℝ) (ht : 0 < t) (hv : 0 < v) :
    |Real.log t| ≤ (t ^ v + t ^ (-v)) / v := by
  have h1 : Real.log t ≤ t ^ v / v := Real.log_le_rpow_div ht.le hv
  have h2 : -Real.log t ≤ t ^ (-v) / v := by
    have := Real.log_le_rpow_div (inv_nonneg.2 ht.le) hv
    rw [Real.log_inv, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le] at this
    exact this
  have h3 : 0 ≤ t ^ v / v := by positivity
  have h4 : 0 ≤ t ^ (-v) / v := by positivity
  rw [abs_le, add_div]
  constructor <;> linarith

theorem rpow_le_rpow_add_rpow (t x e v : ℝ) (ht : 0 < t) (he : |e - x| ≤ v) :
    t ^ e ≤ t ^ (x + v) + t ^ (x - v) := by
  rw [abs_le] at he
  rcases le_or_gt 1 t with h | h
  · exact le_add_of_le_of_nonneg (Real.rpow_le_rpow_of_exponent_le h (by linarith)) (by positivity)
  · exact le_add_of_nonneg_of_le (by positivity) (Real.rpow_le_rpow_of_exponent_ge ht h.le (by linarith))

theorem differentiableAt_setIntegral_cpow_smul (S : Set ℝ) (hS : MeasurableSet S) (hS0 : S ⊆ Ioi 0)
    (g : ℝ → ℂ) (hg : AEStronglyMeasurable g (volume.restrict S)) (p q : ℝ)
    (hint : ∀ σ : ℝ, p < σ → σ < q → IntegrableOn (fun t : ℝ => t ^ (σ - 1) * ‖g t‖) S)
    (z : ℂ) (hpz : p < z.re) (hzq : z.re < q) :
    DifferentiableAt ℂ (fun w : ℂ => ∫ t in S, (t : ℂ) ^ (w - 1) • g t) z := by
  set F : ℂ → ℝ → ℂ := fun w t => (t : ℂ) ^ (w - 1) • g t with hF
  set F' : ℂ → ℝ → ℂ := fun w t => ((t : ℂ) ^ (w - 1) * (Real.log t : ℂ)) • g t with hF'

  obtain ⟨v, hv0, hv1, hv2⟩ : ∃ v : ℝ, 0 < v ∧ p < z.re - 2 * v ∧ z.re + 2 * v < q :=
    ⟨min ((z.re - p) / 4) ((q - z.re) / 4), by
      refine ⟨lt_min (by linarith) (by linarith), ?_, ?_⟩
      · have := min_le_left ((z.re - p) / 4) ((q - z.re) / 4); linarith
      · have := min_le_right ((z.re - p) / 4) ((q - z.re) / 4); linarith⟩
  set bound : ℝ → ℝ := fun t =>
    (t ^ (z.re + 2 * v - 1) + t ^ (z.re - 1) + t ^ (z.re - 1) + t ^ (z.re - 2 * v - 1)) * ‖g t‖ / v with hbound
  have hcpow_cont : ∀ w : ℂ, ContinuousOn (fun t : ℝ => (t : ℂ) ^ (w - 1)) S := fun w =>
    continuousOn_of_forall_continuousAt fun t ht =>
      continuousAt_ofReal_cpow_const _ _ (Or.inr (hS0 ht).ne')
  have hlog_cont : ContinuousOn (fun t : ℝ => (Real.log t : ℂ)) S :=
    continuous_ofReal.comp_continuousOn
      (continuousOn_log.mono fun t ht => (hS0 ht).ne')
  have h1 : ∀ᶠ w : ℂ in 𝓝 z, AEStronglyMeasurable (F w) (volume.restrict S) :=
    Eventually.of_forall fun w => ((hcpow_cont w).aestronglyMeasurable hS).smul hg

  have hFint : ∀ w : ℂ, p < w.re → w.re < q → Integrable (F w) (volume.restrict S) := by
    intro w hw1 hw2
    have hi : Integrable (fun t : ℝ => t ^ (w.re - 1) * ‖g t‖) (volume.restrict S) := hint w.re hw1 hw2
    refine hi.mono' (((hcpow_cont w).aestronglyMeasurable hS).smul hg) ?_
    refine (ae_restrict_mem hS).mono fun t ht => ?_
    rw [hF]
    simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos (hS0 ht), sub_re, one_re]
    exact le_rfl
  have h2 : Integrable (F z) (volume.restrict S) := hFint z hpz hzq
  have h3 : AEStronglyMeasurable (F' z) (volume.restrict S) :=
    (((hcpow_cont z).mul hlog_cont).aestronglyMeasurable hS).smul hg

  have h4 : ∀ᵐ t : ℝ ∂volume.restrict S, ∀ w : ℂ, w ∈ Metric.ball z v → ‖F' w t‖ ≤ bound t := by
    refine (ae_restrict_mem hS).mono fun t ht w hw => ?_
    have ht0 : 0 < t := hS0 ht
    rw [hF', hbound]
    simp only [norm_smul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re,
      Complex.norm_real, Real.norm_eq_abs]
    have hwz : |(w.re - 1) - (z.re - 1)| ≤ v := by
      rw [mem_ball_iff_norm] at hw
      have := abs_re_le_norm (w - z)
      rw [sub_re] at this
      have : |w.re - z.re| ≤ v := this.trans hw.le
      simpa using this
    have hp1 : t ^ (w.re - 1) ≤ t ^ (z.re - 1 + v) + t ^ (z.re - 1 - v) :=
      rpow_le_rpow_add_rpow t (z.re - 1) (w.re - 1) v ht0 hwz
    have hp2 : |Real.log t| ≤ (t ^ v + t ^ (-v)) / v := abs_log_le_rpow_add t v ht0 hv0
    have hprod : t ^ (w.re - 1) * |Real.log t| ≤
        (t ^ (z.re - 1 + v) + t ^ (z.re - 1 - v)) * ((t ^ v + t ^ (-v)) / v) :=
      mul_le_mul hp1 hp2 (abs_nonneg _) (by positivity)
    have hexp : (t ^ (z.re - 1 + v) + t ^ (z.re - 1 - v)) * ((t ^ v + t ^ (-v)) / v) =
        (t ^ (z.re + 2 * v - 1) + t ^ (z.re - 1) + t ^ (z.re - 1) + t ^ (z.re - 2 * v - 1)) / v := by
      rw [add_mul, mul_div_assoc', mul_div_assoc', mul_add, mul_add, ← Real.rpow_add ht0, ← Real.rpow_add ht0,
        ← Real.rpow_add ht0, ← Real.rpow_add ht0, ← add_div]
      congr 1
      ring_nf
    calc t ^ (w.re - 1) * |Real.log t| * ‖g t‖
        ≤ (t ^ (z.re - 1 + v) + t ^ (z.re - 1 - v)) * ((t ^ v + t ^ (-v)) / v) * ‖g t‖ :=
          mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
      _ = _ := by rw [hexp]; ring

  have h5 : Integrable bound (volume.restrict S) := by
    have hi1 := hint (z.re + 2 * v) (by linarith) hv2
    have hi2 := hint z.re hpz hzq
    have hi3 := hint (z.re - 2 * v) hv1 (by linarith)
    have : bound = fun t => ((t ^ (z.re + 2 * v - 1) * ‖g t‖ + t ^ (z.re - 1) * ‖g t‖) +
        (t ^ (z.re - 1) * ‖g t‖ + t ^ (z.re - 2 * v - 1) * ‖g t‖)) / v := by
      funext t; rw [hbound]; ring
    rw [this]
    exact ((hi1.add hi2).add (hi2.add hi3)).div_const v

  have h6 : ∀ᵐ t : ℝ ∂volume.restrict S, ∀ w : ℂ, w ∈ Metric.ball z v →
      HasDerivAt (fun w : ℂ => F w t) (F' w t) w := by
    refine (ae_restrict_mem hS).mono fun t ht w _ => ?_
    have ht0 : 0 < t := hS0 ht
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
    have u1 : HasDerivAt (fun w : ℂ => (t : ℂ) ^ (w - 1)) ((t : ℂ) ^ (w - 1) * (Real.log t : ℂ)) w := by
      have := ((hasDerivAt_id' w).sub_const 1).const_cpow (Or.inl ht')
      rw [ofReal_log ht0.le]
      convert this using 1
      ring
    exact u1.smul_const (g t)
  have main := hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds _ hv0) h1 h2 h3 h4 h5 h6
  exact main.2.differentiableAt

theorem integrableOn_tail (f : ℝ → ℂ) (hf : ContinuousOn f (Ioi 0)) (σ₀ : ℝ)
    (hmel : ∀ s : ℂ, σ₀ < s.re → MellinConvergent f s) (σ : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ (σ - 1) * ‖f t‖) (Ioi 1) := by
  set s' : ℝ := max σ₀ σ + 1 with hs'
  have h0 : σ₀ < s' := by have := le_max_left σ₀ σ; linarith
  have h0' : σ ≤ s' := by have := le_max_right σ₀ σ; linarith
  have h1 : σ₀ < ((s' : ℂ)).re := by simpa using h0
  have h2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((s' : ℂ) - 1) • f t) (Ioi 1) :=
    (hmel _ h1).mono_set (Ioi_subset_Ioi zero_le_one)
  have hmeas : AEStronglyMeasurable (fun t : ℝ => t ^ (σ - 1) * ‖f t‖) (volume.restrict (Ioi 1)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul ?_ ((hf.mono (Ioi_subset_Ioi zero_le_one)).norm)
    exact continuousOn_of_forall_continuousAt fun t ht =>
      Real.continuousAt_rpow_const _ _ (Or.inl (zero_lt_one.trans ht).ne')
  refine Integrable.mono' h2.norm hmeas ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
  have ht0 : 0 < t := zero_lt_one.trans ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_smul,
    Complex.norm_cpow_eq_rpow_re_of_pos ht0]
  simp only [sub_re, ofReal_re, one_re]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le ht.le (by linarith)) (norm_nonneg _)

theorem differentiable_tail (f : ℝ → ℂ) (hf : ContinuousOn f (Ioi 0)) (σ₀ : ℝ)
    (hmel : ∀ s : ℂ, σ₀ < s.re → MellinConvergent f s) :
    Differentiable ℂ (fun w : ℂ => ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) • f t) := fun z =>
  differentiableAt_setIntegral_cpow_smul (Ioi 1) measurableSet_Ioi (Ioi_subset_Ioi zero_le_one) f
    ((hf.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi) (z.re - 1) (z.re + 1)
    (fun σ _ _ => integrableOn_tail f hf σ₀ hmel σ) z (by linarith) (by linarith)

theorem differentiableAt_head (r : ℝ → ℂ) (hr : ContinuousOn r (Ioc 0 1)) (e C : ℝ)
    (hbound : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖r t‖ ≤ C * t ^ e) (z : ℂ) (hz : -e < z.re) :
    DifferentiableAt ℂ (fun w : ℂ => ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w - 1) • r t) z := by
  refine differentiableAt_setIntegral_cpow_smul (Ioc 0 1) measurableSet_Ioc Ioc_subset_Ioi_self r
    (hr.aestronglyMeasurable measurableSet_Ioc) (-e) (z.re + 1) (fun σ hσ _ => ?_) z hz (by linarith)

  have hmeas : AEStronglyMeasurable (fun t : ℝ => t ^ (σ - 1) * ‖r t‖) (volume.restrict (Ioc 0 1)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    refine ContinuousOn.mul ?_ hr.norm
    exact continuousOn_of_forall_continuousAt fun t ht =>
      Real.continuousAt_rpow_const _ _ (Or.inl ht.1.ne')
  have hint : IntegrableOn (fun t : ℝ => C * t ^ (σ - 1 + e)) (Ioc 0 1) := by
    have h1 : IntegrableOn (fun t : ℝ => t ^ (σ - 1 + e)) (Ioo 0 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith)
    have h2 : IntegrableOn (fun t : ℝ => t ^ (σ - 1 + e)) (Ioc 0 1) :=
      (integrableOn_Ioc_iff_integrableOn_Ioo (f := fun t : ℝ => t ^ (σ - 1 + e)) (μ := volume)).mpr h1
    exact h2.const_mul C
  refine Integrable.mono' hint hmeas ?_
  refine (ae_restrict_mem measurableSet_Ioc).mono fun t ht => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by have := ht.1; positivity), Real.rpow_add ht.1]
  calc t ^ (σ - 1) * ‖r t‖ ≤ t ^ (σ - 1) * (C * t ^ e) :=
        mul_le_mul_of_nonneg_left (hbound t ht.1 ht.2) (by have := ht.1; positivity)
    _ = C * (t ^ (σ - 1) * t ^ e) := by ring

theorem Ioc_union_Ioi : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := Ioc_union_Ioi_eq_Ioi zero_le_one

theorem disjoint_Ioc_Ioi : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) :=
  disjoint_left.mpr fun t ht ht' => (not_lt.mpr ht.2) ht'

theorem mellin_eq_head_add_tail (f : ℝ → ℂ) (w : ℂ) (h : MellinConvergent f w) :
    mellin f w = (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w - 1) • f t) + ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) • f t := by
  rw [mellin, ← Ioc_union_Ioi]
  exact setIntegral_union disjoint_Ioc_Ioi measurableSet_Ioi (h.mono_set Ioc_subset_Ioi_self)
    (h.mono_set (Ioi_subset_Ioi zero_le_one))

theorem integrableOn_cpow_Ioc_and_integral_eq (a w : ℂ) (h : 0 < w.re + a.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) • ((t : ℂ) ^ a)) (Ioc 0 1) ∧
      ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w - 1) • ((t : ℂ) ^ a) = 1 / (w + a) := by
  obtain ⟨hconv, hval⟩ := hasMellin_cpow_Ioc a h
  have hpt : ∀ t : ℝ, (t : ℂ) ^ (w - 1) • indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a) t =
      indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ (w - 1) • ((t : ℂ) ^ a)) t := by
    intro t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · rw [indicator_of_mem ht, indicator_of_mem ht]
    · rw [indicator_of_notMem ht, indicator_of_notMem ht, smul_zero]
  rw [MellinConvergent] at hconv
  rw [mellin] at hval
  simp_rw [hpt] at hconv hval
  rw [integrableOn_indicator_iff measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self] at hconv
  rw [setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr Ioc_subset_Ioi_self] at hval
  exact ⟨hconv, hval⟩

theorem differentiableAt_Gammaℂ (s : ℂ) (hs : 0 < s.re) : DifferentiableAt ℂ Complex.Gammaℂ s := by
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (2 : ℂ) * (2 * (π : ℂ)) ^ (-s)) s := by
    refine (DifferentiableAt.const_cpow differentiableAt_id.neg ?_).const_mul _
    left; exact mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_pos.ne')
  have h2 : DifferentiableAt ℂ Complex.Gamma s :=
    Complex.differentiableAt_Gamma s fun m h => by
      have := congrArg Complex.re h; simp at this; linarith
  have : Complex.Gammaℂ = fun s : ℂ => (2 : ℂ) * (2 * (π : ℂ)) ^ (-s) * Complex.Gamma s := by
    funext s; rw [Complex.Gammaℂ]
  rw [this]
  exact h1.mul h2

theorem pos_case (ν : ℝ) (hν : 0 < ν) (f : ℝ → ℂ) (hf : ContinuousOn f (Ioi 0))
    (c : ℂ) (δ : ℝ) (hδ : 0 < δ) (C : ℝ)
    (hnear : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y - c * (y : ℂ) ^ ((1 / 2 - ν : ℝ) : ℂ)‖ ≤ C * y ^ (1 / 2 - ν + δ))
    (σ₀ : ℝ) (Ψ : ℂ → ℂ) (hΨ : Differentiable ℂ Ψ)
    (hmel : ∀ s : ℂ, σ₀ < s.re →
      MellinConvergent f s ∧ mellin f s = Complex.Gammaℂ (s + 1 / 2 + (ν : ℂ)) * Ψ s) :
    c = 0 := by
  set a : ℂ := ((1 / 2 - ν : ℝ) : ℂ) with ha
  have hare : a.re = 1 / 2 - ν := by simp [ha]
  set r : ℝ → ℂ := fun t => f t - c * (t : ℂ) ^ a with hr
  have hr_cont : ContinuousOn r (Ioc 0 1) := by
    refine (hf.mono Ioc_subset_Ioi_self).sub (ContinuousOn.mul continuousOn_const ?_)
    exact continuousOn_of_forall_continuousAt fun t ht => continuousAt_ofReal_cpow_const _ _ (Or.inr ht.1.ne')
  set Hr : ℂ → ℂ := fun w => ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w - 1) • r t with hHr
  set T : ℂ → ℂ := fun w => ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) • f t with hT
  have hHr_diff : ∀ z : ℂ, ν - 1 / 2 - δ < z.re → DifferentiableAt ℂ Hr z := fun z hz =>
    differentiableAt_head r hr_cont (1 / 2 - ν + δ) C (fun t ht ht' => hnear t ht ht') z (by linarith)
  have hT_diff : Differentiable ℂ T := differentiable_tail f hf σ₀ (fun s hs => (hmel s hs).1)

  have hdecomp : ∀ w : ℂ, σ₀ < w.re → ν - 1 / 2 < w.re →
      c * (1 / (w + a)) + Hr w + T w = Complex.Gammaℂ (w + 1 / 2 + (ν : ℂ)) * Ψ w := by
    intro w hw1 hw2
    obtain ⟨hconv, hval⟩ := hmel w hw1
    have hwa : 0 < w.re + a.re := by rw [hare]; linarith
    obtain ⟨hIa, hvala⟩ := integrableOn_cpow_Ioc_and_integral_eq a w hwa
    have hIf : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) • f t) (Ioc 0 1) := hconv.mono_set Ioc_subset_Ioi_self
    have hImain : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) • (c * (t : ℂ) ^ a)) (Ioc 0 1) := by
      have h1 : IntegrableOn (fun t : ℝ => c * ((t : ℂ) ^ (w - 1) • ((t : ℂ) ^ a))) (Ioc 0 1) := hIa.const_mul c
      refine h1.congr_fun (fun t _ => ?_) measurableSet_Ioc
      simp only [smul_eq_mul]; ring
    have hIr : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) • r t) (Ioc 0 1) := by
      have h1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) • f t - (t : ℂ) ^ (w - 1) • (c * (t : ℂ) ^ a))
          (Ioc 0 1) := hIf.sub hImain
      refine h1.congr_fun (fun t _ => ?_) measurableSet_Ioc
      simp only [hr, smul_eq_mul]; ring
    have hhead : ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w - 1) • f t = c * (1 / (w + a)) + Hr w := by
      have hsplit : (fun t : ℝ => (t : ℂ) ^ (w - 1) • f t) =
          fun t : ℝ => (t : ℂ) ^ (w - 1) • (c * (t : ℂ) ^ a) + (t : ℂ) ^ (w - 1) • r t := by
        funext t; simp only [hr, smul_eq_mul]; ring
      rw [hsplit, integral_add hImain hIr, hHr]
      congr 1
      rw [← hvala, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
      simp only [smul_eq_mul]; ring
    rw [← hval, mellin_eq_head_add_tail f w hconv, hhead, hT]

  set δ' : ℝ := min δ ν with hδ'
  have hδ'pos : 0 < δ' := lt_min hδ hν
  set U : Set ℂ := {w | ν - 1 / 2 - δ' < w.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt _).isPreconnected
  set L : ℂ → ℂ := fun w => (w + a) * (Hr w + T w) + c with hL
  set R : ℂ → ℂ := fun w => (w + a) * (Complex.Gammaℂ (w + 1 / 2 + (ν : ℂ)) * Ψ w) with hR
  have hLdiff : DifferentiableOn ℂ L U := by
    intro w hw
    have hw' : ν - 1 / 2 - δ < w.re := by
      have : δ' ≤ δ := min_le_left _ _; simp only [hU, mem_setOf_eq] at hw; linarith
    exact (((differentiableAt_id.add_const a).mul ((hHr_diff w hw').add (hT_diff w))).add_const c).differentiableWithinAt
  have hRdiff : DifferentiableOn ℂ R U := by
    intro w hw
    simp only [hU, mem_setOf_eq] at hw
    have hre : 0 < (w + 1 / 2 + (ν : ℂ)).re := by
      have : δ' ≤ ν := min_le_right _ _
      simp; linarith
    have hG : DifferentiableAt ℂ (fun w : ℂ => Complex.Gammaℂ (w + 1 / 2 + (ν : ℂ))) w :=
      (differentiableAt_Gammaℂ _ hre).comp w ((differentiableAt_id.add_const _).add_const _)
    exact ((differentiableAt_id.add_const a).mul (hG.mul (hΨ w))).differentiableWithinAt

  set x₀ : ℝ := max σ₀ (ν - 1 / 2) + 1 with hx₀
  have hx1 : σ₀ < x₀ := by have := le_max_left σ₀ (ν - 1 / 2); linarith
  have hx2 : ν - 1 / 2 < x₀ := by have := le_max_right σ₀ (ν - 1 / 2); linarith
  have hz₀U : ((x₀ : ℂ)) ∈ U := by
    simp only [hU, mem_setOf_eq, ofReal_re]; linarith
  have hagree : L =ᶠ[𝓝 ((x₀ : ℂ))] R := by
    have hV : {w : ℂ | σ₀ < w.re ∧ ν - 1 / 2 < w.re} ∈ 𝓝 ((x₀ : ℂ)) := by
      refine IsOpen.mem_nhds ?_ ?_
      · exact (isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt continuous_const Complex.continuous_re)
      · simp only [mem_setOf_eq, ofReal_re]; exact ⟨hx1, hx2⟩
    filter_upwards [hV] with w hw
    have h := hdecomp w hw.1 hw.2
    have hwa : w + a ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; rw [add_re, hare] at this; simp at this; linarith
    simp only [hL, hR]
    rw [← h]
    field_simp
    ring
  have hEq : EqOn L R U :=
    (hLdiff.analyticOnNhd hUopen).eqOn_of_preconnected_of_eventuallyEq (hRdiff.analyticOnNhd hUopen)
      hUconn hz₀U hagree

  have hstarU : (((ν - 1 / 2 : ℝ)) : ℂ) ∈ U := by
    simp only [hU, mem_setOf_eq, ofReal_re]; linarith
  have hstar := hEq hstarU
  have hwa0 : (((ν - 1 / 2 : ℝ)) : ℂ) + a = 0 := by rw [ha]; push_cast; ring
  simp only [hL, hR, hwa0, zero_mul, zero_add] at hstar
  exact hstar

theorem integrableOn_log_cpow_Ioc_and_integral_eq (w : ℂ) (hw : -(1 / 2 : ℝ) < w.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) • ((Real.log t : ℂ) * (t : ℂ) ^ (1 / 2 : ℂ))) (Ioc 0 1) ∧
      ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w - 1) • ((Real.log t : ℂ) * (t : ℂ) ^ (1 / 2 : ℂ)) =
        -1 / (w + 1 / 2) ^ 2 := by
  set g : ℝ → ℂ := indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ (1 / 2 : ℂ)) with hg

  have hgint : IntegrableOn g (Ioi 0) := by
    have h := (integrableOn_cpow_Ioc_and_integral_eq (1 / 2 : ℂ) 1 (by norm_num)).1
    have h' : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (1 / 2 : ℂ)) (Ioc 0 1) := by
      refine h.congr_fun (fun t _ => ?_) measurableSet_Ioc
      simp
    rw [hg, integrableOn_indicator_iff measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self]
    exact h'
  have hfc : LocallyIntegrableOn g (Ioi 0) := hgint.locallyIntegrableOn

  have hf_top : g =O[atTop] (fun t : ℝ => t ^ (-(w.re + 1))) := by
    have h0 : g =ᶠ[atTop] (fun _ => (0 : ℂ)) := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
      rw [hg, indicator_of_notMem]
      exact fun h => (not_lt.mpr h.2) ht
    exact h0.trans_isBigO (isBigO_zero _ _)
  have hf_bot : g =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(-(1 / 2) : ℝ))) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    rw [hg, indicator_of_mem ht, Complex.norm_cpow_eq_rpow_re_of_pos ht.1, one_mul, Real.norm_eq_abs,
      abs_of_nonneg (by have := ht.1; positivity)]
    norm_num
  obtain ⟨hconv, hder⟩ := mellin_hasDerivAt_of_isBigO_rpow hfc hf_top (by linarith) hf_bot hw

  have hmel_g : ∀ z : ℂ, -(1 / 2 : ℝ) < z.re → mellin g z = 1 / (z + 1 / 2) := by
    intro z hz
    have := (hasMellin_cpow_Ioc (1 / 2 : ℂ) (s := z) (by simp; linarith)).2
    simpa [hg] using this
  have hder2 : HasDerivAt (mellin g) (-1 / (w + 1 / 2) ^ 2) w := by
    have hne : w + 1 / 2 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have h1 : HasDerivAt (fun z : ℂ => (z + 1 / 2)⁻¹) (-1 / (w + 1 / 2) ^ 2) w := by
      have h__af := (((hasDerivAt_id w).add_const (1 / 2 : ℂ)).inv hne)
      simp at h__af ⊢
      exact h__af
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw] with z hz
    rw [hmel_g z hz, one_div]
  have hval : mellin (fun t : ℝ => Real.log t • g t) w = -1 / (w + 1 / 2) ^ 2 := hder.unique hder2

  have hpt : ∀ t : ℝ, (t : ℂ) ^ (w - 1) • (Real.log t • g t) =
      indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ (w - 1) • ((Real.log t : ℂ) * (t : ℂ) ^ (1 / 2 : ℂ))) t := by
    intro t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · rw [hg, indicator_of_mem ht, indicator_of_mem ht, Complex.real_smul]
    · rw [hg, indicator_of_notMem ht, indicator_of_notMem ht, smul_zero, smul_zero]
  rw [MellinConvergent] at hconv
  rw [mellin] at hval
  simp_rw [hpt] at hconv hval
  rw [integrableOn_indicator_iff measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self] at hconv
  rw [setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr Ioc_subset_Ioi_self] at hval
  exact ⟨hconv, hval⟩

theorem zero_case (f : ℝ → ℂ) (hf : ContinuousOn f (Ioi 0))
    (a b : ℂ) (δ : ℝ) (hδ : 0 < δ) (C : ℝ)
    (hnear : ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖f y - (a + b * (Real.log y : ℂ)) * (Real.sqrt y : ℂ)‖ ≤ C * y ^ (1 / 2 + δ))
    (σ₀ : ℝ) (Ψ : ℂ → ℂ) (hΨ : Differentiable ℂ Ψ)
    (hmel : ∀ s : ℂ, σ₀ < s.re →
      MellinConvergent f s ∧ mellin f s = Complex.Gammaℂ (s + 1 / 2 + ((0 : ℝ) : ℂ)) * Ψ s) :
    b = 0 := by
  set r : ℝ → ℂ := fun t => f t - (a + b * (Real.log t : ℂ)) * (Real.sqrt t : ℂ) with hr
  have hr_cont : ContinuousOn r (Ioc 0 1) := by
    refine (hf.mono Ioc_subset_Ioi_self).sub (ContinuousOn.mul ?_ ?_)
    · refine continuousOn_const.add (continuousOn_const.mul ?_)
      exact continuous_ofReal.comp_continuousOn (continuousOn_log.mono fun t ht => ht.1.ne')
    · exact continuous_ofReal.comp_continuousOn Real.continuous_sqrt.continuousOn
  set Hr : ℂ → ℂ := fun w => ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w - 1) • r t with hHr
  set T : ℂ → ℂ := fun w => ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) • f t with hT
  have hHr_diff : ∀ z : ℂ, -(1 / 2) - δ < z.re → DifferentiableAt ℂ Hr z := fun z hz =>
    differentiableAt_head r hr_cont (1 / 2 + δ) C (fun t ht ht' => hnear t ht ht') z (by linarith)
  have hT_diff : Differentiable ℂ T := differentiable_tail f hf σ₀ (fun s hs => (hmel s hs).1)

  have hsqrt : ∀ t : ℝ, 0 < t → ((Real.sqrt t : ℝ) : ℂ) = (t : ℂ) ^ (1 / 2 : ℂ) := by
    intro t ht
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ht.le]
    norm_num

  have hdecomp : ∀ w : ℂ, σ₀ < w.re → -(1 / 2 : ℝ) < w.re →
      a * (1 / (w + 1 / 2)) + b * (-1 / (w + 1 / 2) ^ 2) + Hr w + T w =
        Complex.Gammaℂ (w + 1 / 2) * Ψ w := by
    intro w hw1 hw2
    obtain ⟨hconv, hval⟩ := hmel w hw1
    obtain ⟨hIa, hvala⟩ := integrableOn_cpow_Ioc_and_integral_eq (1 / 2 : ℂ) w (by simp; linarith)
    obtain ⟨hIb, hvalb⟩ := integrableOn_log_cpow_Ioc_and_integral_eq w hw2
    have hIf : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) • f t) (Ioc 0 1) := hconv.mono_set Ioc_subset_Ioi_self
    have hImain : IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (w - 1) • ((a + b * (Real.log t : ℂ)) * (Real.sqrt t : ℂ))) (Ioc 0 1) := by
      have h1 : IntegrableOn (fun t : ℝ => a * ((t : ℂ) ^ (w - 1) • ((t : ℂ) ^ (1 / 2 : ℂ))) +
          b * ((t : ℂ) ^ (w - 1) • ((Real.log t : ℂ) * (t : ℂ) ^ (1 / 2 : ℂ)))) (Ioc 0 1) :=
        (hIa.const_mul a).add (hIb.const_mul b)
      refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioc
      simp only [smul_eq_mul, hsqrt t ht.1]; ring
    have hIr : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) • r t) (Ioc 0 1) := by
      have h1 := hIf.sub hImain
      refine h1.congr_fun (fun t _ => ?_) measurableSet_Ioc
      simp only [hr, smul_eq_mul, Pi.sub_apply]; ring
    have hhead : ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w - 1) • f t =
        a * (1 / (w + 1 / 2)) + b * (-1 / (w + 1 / 2) ^ 2) + Hr w := by
      have hsplit : ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w - 1) • f t =
          (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w - 1) • ((a + b * (Real.log t : ℂ)) * (Real.sqrt t : ℂ))) +
            ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w - 1) • r t := by
        rw [← integral_add hImain hIr]
        refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
        simp only [hr, smul_eq_mul]; ring
      have hmain : ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w - 1) • ((a + b * (Real.log t : ℂ)) * (Real.sqrt t : ℂ)) =
          a * (1 / (w + 1 / 2)) + b * (-1 / (w + 1 / 2) ^ 2) := by
        rw [← hvala, ← hvalb, ← integral_const_mul, ← integral_const_mul, ← integral_add (hIa.const_mul a) (hIb.const_mul b)]
        refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
        simp only [smul_eq_mul, hsqrt t ht.1]; ring
      rw [hsplit, hmain, hHr]
    have hval' : mellin f w = Complex.Gammaℂ (w + 1 / 2) * Ψ w := by simpa using hval
    rw [← hval', mellin_eq_head_add_tail f w hconv, hhead, hT]

  set δ' : ℝ := min δ (1 / 2) with hδ'
  have hδ'pos : 0 < δ' := lt_min hδ (by norm_num)
  set U : Set ℂ := {w | -(1 / 2) - δ' < w.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt _).isPreconnected
  set L : ℂ → ℂ := fun w => (w + 1 / 2) ^ 2 * (Hr w + T w) + a * (w + 1 / 2) - b with hL
  set R : ℂ → ℂ := fun w =>
    (w + 1 / 2) * ((2 : ℂ) * (2 * (π : ℂ)) ^ (-(w + 1 / 2)) * Complex.Gamma (w + 3 / 2)) * Ψ w with hR
  have hLdiff : DifferentiableOn ℂ L U := by
    intro w hw
    have hw' : -(1 / 2) - δ < w.re := by
      have : δ' ≤ δ := min_le_left _ _; simp only [hU, mem_setOf_eq] at hw; linarith
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (w + 1 / 2) ^ 2) w := (differentiableAt_id.add_const _).pow 2
    exact (((h1.mul ((hHr_diff w hw').add (hT_diff w))).add
      ((differentiableAt_id.add_const _).const_mul a)).sub_const b).differentiableWithinAt
  have hRdiff : DifferentiableOn ℂ R U := by
    intro w hw
    simp only [hU, mem_setOf_eq] at hw
    have hδ1 : δ' ≤ 1 / 2 := min_le_right _ _
    have hre : 0 < (w + 3 / 2).re := by simp; linarith
    have hG : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w + 3 / 2)) w :=
      (Complex.differentiableAt_Gamma _ fun m h => by
        have := congrArg Complex.re h; simp at this; linarith).comp w (differentiableAt_id.add_const _)
    have hP : DifferentiableAt ℂ (fun w : ℂ => (2 : ℂ) * (2 * (π : ℂ)) ^ (-(w + 1 / 2))) w := by
      refine (DifferentiableAt.const_cpow (differentiableAt_id.add_const _).neg ?_).const_mul _
      left; exact mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_pos.ne')
    exact (((differentiableAt_id.add_const _).mul (hP.mul hG)).mul (hΨ w)).differentiableWithinAt
  set x₀ : ℝ := max σ₀ (-(1 / 2)) + 1 with hx₀
  have hx1 : σ₀ < x₀ := by have := le_max_left σ₀ (-(1 / 2)); linarith
  have hx2 : -(1 / 2 : ℝ) < x₀ := by have := le_max_right σ₀ (-(1 / 2)); linarith
  have hz₀U : ((x₀ : ℂ)) ∈ U := by
    simp only [hU, mem_setOf_eq, ofReal_re]; linarith
  have hagree : L =ᶠ[𝓝 ((x₀ : ℂ))] R := by
    have hV : {w : ℂ | σ₀ < w.re ∧ -(1 / 2 : ℝ) < w.re} ∈ 𝓝 ((x₀ : ℂ)) := by
      refine IsOpen.mem_nhds ?_ ?_
      · exact (isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt continuous_const Complex.continuous_re)
      · simp only [mem_setOf_eq, ofReal_re]; exact ⟨hx1, hx2⟩
    filter_upwards [hV] with w hw
    have h := hdecomp w hw.1 hw.2
    have hwa : w + 1 / 2 ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith [hw.2]
    have hGamma : (w + 1 / 2) * Complex.Gamma (w + 1 / 2) = Complex.Gamma (w + 3 / 2) := by
      rw [← Complex.Gamma_add_one _ hwa]; congr 1; ring
    have hG : Complex.Gammaℂ (w + 1 / 2) = 2 * (2 * (π : ℂ)) ^ (-(w + 1 / 2)) * Complex.Gamma (w + 1 / 2) := by
      rw [Complex.Gammaℂ]
    rw [hG] at h
    have hHT : Hr w + T w = 2 * (2 * (π : ℂ)) ^ (-(w + 1 / 2)) * Complex.Gamma (w + 1 / 2) * Ψ w
        - a * (1 / (w + 1 / 2)) - b * (-1 / (w + 1 / 2) ^ 2) := by
      rw [← h]; ring
    have e1 : (w + 1 / 2) ^ 2 * (a * (1 / (w + 1 / 2))) = a * (w + 1 / 2) := by
      field_simp
    have hsq : (w + 1 / 2) ^ 2 ≠ 0 := pow_ne_zero 2 hwa
    have e2' : (w + 1 / 2) ^ 2 * (-1 / (w + 1 / 2) ^ 2) = -1 := by
      rw [mul_div_assoc', mul_neg_one, neg_div, div_self hsq]
    have e2 : (w + 1 / 2) ^ 2 * (b * (-1 / (w + 1 / 2) ^ 2)) = -b := by
      calc (w + 1 / 2) ^ 2 * (b * (-1 / (w + 1 / 2) ^ 2))
          = b * ((w + 1 / 2) ^ 2 * (-1 / (w + 1 / 2) ^ 2)) := by ring
        _ = -b := by rw [e2', mul_neg_one]
    simp only [hL, hR]
    rw [hHT, ← hGamma]
    linear_combination (-1 : ℂ) * e1 + (-1 : ℂ) * e2
  have hEq : EqOn L R U :=
    (hLdiff.analyticOnNhd hUopen).eqOn_of_preconnected_of_eventuallyEq (hRdiff.analyticOnNhd hUopen)
      hUconn hz₀U hagree
  have hstarU : ((-(1 / 2) : ℝ) : ℂ) ∈ U := by
    simp only [hU, mem_setOf_eq, ofReal_re]; linarith
  have hstar := hEq hstarU
  have hw0 : ((-(1 / 2) : ℝ) : ℂ) + 1 / 2 = 0 := by push_cast; ring
  simp only [hL, hR, hw0] at hstar
  simpa using hstar

end LanglandsTunnell.PoleClash

open LanglandsTunnell.PoleClash in
theorem solution
    (ν : ℝ) (hν : 0 ≤ ν) (f : ℝ → ℂ) (hf : ContinuousOn f (Set.Ioi 0))
    (c a b : ℂ) (δ : ℝ) (hδ : 0 < δ) (C : ℝ)
    (hnear : ∀ y : ℝ, 0 < y → y ≤ 1 →
      (0 < ν → ‖f y - c * (y : ℂ) ^ ((1 / 2 - ν : ℝ) : ℂ)‖ ≤ C * y ^ (1 / 2 - ν + δ)) ∧
      (ν = 0 → ‖f y - (a + b * (Real.log y : ℂ)) * (Real.sqrt y : ℂ)‖ ≤ C * y ^ (1 / 2 + δ)))
    (σ₀ : ℝ) (Ψ : ℂ → ℂ) (hΨ : Differentiable ℂ Ψ)
    (hmel : ∀ s : ℂ, σ₀ < s.re →
      MellinConvergent f s ∧ mellin f s = Complex.Gammaℂ (s + 1 / 2 + (ν : ℂ)) * Ψ s) :
    (0 < ν → c = 0) ∧ (ν = 0 → b = 0) := by
  refine ⟨fun hpos => ?_, fun h0 => ?_⟩
  · exact pos_case ν hpos f hf c δ hδ C (fun y hy hy' => (hnear y hy hy').1 hpos) σ₀ Ψ hΨ hmel
  · subst h0
    exact zero_case f hf a b δ hδ C (fun y hy hy' => (hnear y hy hy').2 rfl) σ₀ Ψ hΨ hmel

end

end S_LanglandsTunnell_eq_zero_of_mellin_eq_GammaC_mul_of_sub_rpow_bound_near_zero
end P2MW
export P2MW.S_LanglandsTunnell_eq_zero_of_mellin_eq_GammaC_mul_of_sub_rpow_bound_near_zero (solution)
