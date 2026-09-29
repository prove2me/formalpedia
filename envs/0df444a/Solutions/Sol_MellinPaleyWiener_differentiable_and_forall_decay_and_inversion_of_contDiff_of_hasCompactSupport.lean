-- Prove2me | solution 1 for MellinPaleyWiener.differentiable_and_forall_decay_and_inversion_of_contDiff_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b2ed950b-428f-5378-905c-c55356516cb9

import Theorems.Thm_Complex_differentiableOn_integral_of_continuousOn_of_forall_differentiableOn
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MellinPaleyWiener_differentiable_and_forall_decay_and_inversion_of_contDiff_of_hasCompactSupport

set_option autoImplicit false

open MeasureTheory Real Complex
open scoped FourierTransform RealInnerProductSpace Topology ENNReal

namespace MPW

noncomputable def g (h : ℝ → ℂ) (σ : ℝ) : ℝ → ℂ := fun u => h u * cexp ((σ : ℂ) * (u : ℂ))

theorem g_apply (h : ℝ → ℂ) (σ u : ℝ) : g h σ u = h u * cexp ((σ : ℂ) * (u : ℂ)) := rfl

theorem contDiff_cexp_mul (σ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => cexp ((σ : ℂ) * (u : ℂ))) :=
  (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

theorem g_contDiff {h : ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (g h σ) :=
  hh.mul (contDiff_cexp_mul σ)

theorem g_hasCompactSupport {h : ℝ → ℂ} (hhc : HasCompactSupport h) (σ : ℝ) : HasCompactSupport (g h σ) :=
  hhc.mul_right

theorem g_integrable {h : ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h) (σ : ℝ) :
    Integrable (g h σ) :=
  (g_contDiff hh σ).continuous.integrable_of_hasCompactSupport (g_hasCompactSupport hhc σ)

theorem M_eq_fourier (h : ℝ → ℂ) (σ t : ℝ) :
    (∫ u : ℝ, h u * cexp (((σ : ℂ) + (t : ℂ) * I) * (u : ℂ))) = 𝓕 (g h σ) (-t / (2 * π)) := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show h u * cexp (((σ : ℂ) + (t : ℂ) * I) * (u : ℂ)) =
    cexp ((↑(-2 * π * inner ℝ u (-t / (2 * π)))) * I) • g h σ u
  rw [g_apply, smul_eq_mul, RCLike.inner_apply, conj_trivial]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have h1 : (-2 * π * (-t / (2 * π) * u) : ℝ) = t * u := by field_simp
  rw [h1, add_mul, Complex.exp_add]
  push_cast
  ring

end MPW

namespace MPW

theorem hasDerivAt_cexp_mul (σ : ℂ) (u : ℝ) :
    HasDerivAt (fun u : ℝ => cexp (σ * (u : ℂ))) (σ * cexp (σ * (u : ℂ))) u := by
  have h1 : HasDerivAt (fun u : ℝ => σ * (u : ℂ)) (σ * 1) u := (hasDerivAt_id u).ofReal_comp.const_mul σ
  have h2 := h1.cexp
  simpa [mul_comm] using h2

theorem iteratedDeriv_const_mul_cexp (c σ : ℂ) :
    ∀ m : ℕ, iteratedDeriv m (fun u : ℝ => c * cexp (σ * (u : ℂ))) = fun u : ℝ => c * σ ^ m * cexp (σ * (u : ℂ)) := by
  intro m
  induction m with
  | zero => funext u; simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    have h := ((hasDerivAt_cexp_mul σ u).const_mul (c * σ ^ m)).deriv
    rw [h]; ring

theorem iteratedDeriv_cexp (σ : ℂ) (m : ℕ) :
    iteratedDeriv m (fun u : ℝ => cexp (σ * (u : ℂ))) = fun u : ℝ => σ ^ m * cexp (σ * (u : ℂ)) := by
  have h := iteratedDeriv_const_mul_cexp 1 σ m
  simp only [one_mul] at h
  exact h

theorem hasCompactSupport_iteratedDeriv {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    ∀ k : ℕ, HasCompactSupport (iteratedDeriv k f) := by
  intro k
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem tsupport_iteratedDeriv_subset (f : ℝ → ℂ) : ∀ k : ℕ, tsupport (iteratedDeriv k f) ⊆ tsupport f := by
  intro k
  induction k with
  | zero => simp
  | succ k ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

theorem tsupport_g_subset (h : ℝ → ℂ) (σ : ℝ) : tsupport (g h σ) ⊆ tsupport h := by
  refine closure_mono ?_
  intro u hu
  simp only [Function.mem_support, ne_eq, g_apply, mul_eq_zero, not_or] at hu ⊢
  exact hu.1

theorem exists_bound_iteratedDeriv_g {h : ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h)
    (k : ℕ) (σ₀ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ σ : ℝ, |σ| ≤ σ₀ → ∀ u : ℝ, ‖iteratedDeriv k (g h σ) u‖ ≤ B := by

  have hH : ∀ i : ℕ, ∃ H : ℝ, ∀ u, ‖iteratedDeriv i h u‖ ≤ H := fun i =>
    (hh.continuous_iteratedDeriv i (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hasCompactSupport_iteratedDeriv hhc i)
  choose H hH' using hH

  obtain ⟨R, hR⟩ := (hhc.isCompact.isBounded).subset_closedBall 0
  by_cases hσ₀ : σ₀ < 0
  · exact ⟨0, le_rfl, fun σ hσ => absurd (lt_of_le_of_lt ((abs_nonneg σ).trans hσ) hσ₀) (lt_irrefl _)⟩
  push_neg at hσ₀
  set B : ℝ := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * |H i| * (σ₀ ^ (k - i) * Real.exp (σ₀ * |R|)) with hB
  refine ⟨B, ?_, fun σ hσ u => ?_⟩
  · refine Finset.sum_nonneg fun i _ => ?_
    positivity
  by_cases hu : u ∈ tsupport h
  · have hk : ((k : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
    have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hh (contDiff_cexp_mul σ) u (n := k) hk
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hmul
    refine hmul.trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp]
    have huR : |u| ≤ |R| := by
      have := hR hu
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
      exact this.trans (le_abs_self R)
    have h1 : ‖iteratedDeriv i h u‖ ≤ |H i| := (hH' i u).trans (le_abs_self _)
    have h2 : ‖((σ : ℂ)) ^ (k - i) * cexp ((σ : ℂ) * (u : ℂ))‖ ≤ σ₀ ^ (k - i) * Real.exp (σ₀ * |R|) := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
      have hre : ((σ : ℂ) * (u : ℂ)).re = σ * u := by simp
      rw [hre]
      refine mul_le_mul (pow_le_pow_left₀ (abs_nonneg σ) hσ _) ?_ (Real.exp_pos _).le (pow_nonneg hσ₀ _)
      refine Real.exp_le_exp.2 ?_
      calc σ * u ≤ |σ * u| := le_abs_self _
        _ = |σ| * |u| := abs_mul σ u
        _ ≤ σ₀ * |R| := mul_le_mul hσ huR (abs_nonneg u) hσ₀
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (norm_nonneg _) (by positivity)
  · have h0 : iteratedDeriv k (g h σ) u = 0 :=
      image_eq_zero_of_notMem_tsupport fun hu' => hu ((tsupport_iteratedDeriv_subset (g h σ) k).trans (tsupport_g_subset h σ) hu')
    rw [h0, norm_zero]
    refine Finset.sum_nonneg fun i _ => ?_
    positivity

end MPW

namespace MPW

theorem integrable_iteratedDeriv_g {h : ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h)
    (σ : ℝ) (k : ℕ) : Integrable (iteratedDeriv k (g h σ)) :=
  ((g_contDiff hh σ).continuous_iteratedDeriv k (by exact_mod_cast le_top)).integrable_of_hasCompactSupport
    (hasCompactSupport_iteratedDeriv (g_hasCompactSupport hhc σ) k)

theorem exists_l1_bound {h : ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h)
    (k : ℕ) (σ₀ : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ σ : ℝ, |σ| ≤ σ₀ → (∫ u : ℝ, ‖iteratedDeriv k (g h σ) u‖) ≤ L := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_iteratedDeriv_g hh hhc k σ₀
  have hfin : volume (tsupport h) < ∞ := hhc.isCompact.measure_lt_top
  refine ⟨B * volume.real (tsupport h), mul_nonneg hB0 ENNReal.toReal_nonneg, fun σ hσ => ?_⟩
  have hzero : ∀ u, u ∉ tsupport h → ‖iteratedDeriv k (g h σ) u‖ = 0 := fun u hu => by
    rw [norm_eq_zero]
    exact image_eq_zero_of_notMem_tsupport fun hu' =>
      hu ((tsupport_iteratedDeriv_subset (g h σ) k).trans (tsupport_g_subset h σ) hu')
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := tsupport h) (fun u hu => hzero u hu)]
  have h1 := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := fun u => ‖iteratedDeriv k (g h σ) u‖) hfin
    (fun u _ => by rw [norm_norm]; exact hB σ hσ u)
  refine le_trans ?_ h1
  exact Real.le_norm_self _

theorem norm_fourier_le (f : ℝ → ℂ) (x : ℝ) : ‖𝓕 f x‖ ≤ ∫ u : ℝ, ‖f u‖ := by
  rw [Real.fourier_eq']
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show ‖cexp (↑(-2 * π * inner ℝ u x) * I) • f u‖ = ‖f u‖
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem pow_mul_norm_M_eq {h : ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h)
    (σ t : ℝ) (n : ℕ) :
    |t| ^ n * ‖∫ u : ℝ, h u * cexp (((σ : ℂ) + (t : ℂ) * I) * (u : ℂ))‖ =
      ‖𝓕 (iteratedDeriv n (g h σ)) (-t / (2 * π))‖ := by
  rw [M_eq_fourier, Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) (g_contDiff hh σ)
    (fun m _ => integrable_iteratedDeriv_g hh hhc σ m) (by exact_mod_cast le_top)]
  rw [norm_smul, norm_pow]
  congr 1
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have : (2 * (π : ℂ) * I * ((-t / (2 * π) : ℝ) : ℂ)) = ((-t : ℝ) : ℂ) * I := by
    push_cast; field_simp
  rw [this, Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg]

end MPW

namespace MPW

theorem one_add_pow_le (t : ℝ) (n : ℕ) : (1 + |t|) ^ n ≤ 2 ^ n * (1 + |t| ^ n) := by
  have h0 : 0 ≤ |t| ^ n := pow_nonneg (abs_nonneg t) n
  by_cases ht : |t| ≤ 1
  · calc (1 + |t|) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ ≤ 2 ^ n * (1 + |t| ^ n) := le_mul_of_one_le_right (by positivity) (by linarith)
  · have ht' : 1 ≤ |t| := le_of_lt (lt_of_not_ge ht)
    calc (1 + |t|) ^ n ≤ (2 * |t|) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = 2 ^ n * |t| ^ n := mul_pow 2 |t| n
      _ ≤ 2 ^ n * (1 + |t| ^ n) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem decay {h : ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h) (n : ℕ) (σ₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ → ∀ t : ℝ,
      (1 + |t|) ^ n * ‖∫ u : ℝ, h u * cexp (((σ' : ℂ) + (t : ℂ) * I) * (u : ℂ))‖ ≤ C := by
  obtain ⟨L₀, hL₀0, hL₀⟩ := exists_l1_bound hh hhc 0 σ₀
  obtain ⟨Ln, hLn0, hLn⟩ := exists_l1_bound hh hhc n σ₀
  refine ⟨2 ^ n * (L₀ + Ln), by positivity, fun σ hσ t => ?_⟩
  have hM0 : ‖∫ u : ℝ, h u * cexp (((σ : ℂ) + (t : ℂ) * I) * (u : ℂ))‖ ≤ L₀ := by
    have h1 := pow_mul_norm_M_eq hh hhc σ t 0
    rw [pow_zero, one_mul] at h1
    rw [h1]
    exact (norm_fourier_le _ _).trans (hL₀ σ hσ)
  have hMn : |t| ^ n * ‖∫ u : ℝ, h u * cexp (((σ : ℂ) + (t : ℂ) * I) * (u : ℂ))‖ ≤ Ln := by
    rw [pow_mul_norm_M_eq hh hhc σ t n]
    exact (norm_fourier_le _ _).trans (hLn σ hσ)
  have hpos : 0 ≤ ‖∫ u : ℝ, h u * cexp (((σ : ℂ) + (t : ℂ) * I) * (u : ℂ))‖ := norm_nonneg _
  calc (1 + |t|) ^ n * ‖∫ u : ℝ, h u * cexp (((σ : ℂ) + (t : ℂ) * I) * (u : ℂ))‖
      ≤ 2 ^ n * (1 + |t| ^ n) * ‖∫ u : ℝ, h u * cexp (((σ : ℂ) + (t : ℂ) * I) * (u : ℂ))‖ :=
        mul_le_mul_of_nonneg_right (one_add_pow_le t n) hpos
    _ = 2 ^ n * (‖∫ u : ℝ, h u * cexp (((σ : ℂ) + (t : ℂ) * I) * (u : ℂ))‖ +
          |t| ^ n * ‖∫ u : ℝ, h u * cexp (((σ : ℂ) + (t : ℂ) * I) * (u : ℂ))‖) := by ring
    _ ≤ 2 ^ n * (L₀ + Ln) := mul_le_mul_of_nonneg_left (add_le_add hM0 hMn) (by positivity)

theorem differentiable_M {h : ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h) :
    Differentiable ℂ (fun s : ℂ => ∫ u : ℝ, h u * cexp (s * (u : ℂ))) := by
  have h1 := Complex.differentiableOn_integral_of_continuousOn_of_forall_differentiableOn
    (volume : Measure ℝ) isOpen_univ hhc (fun s u => h u * cexp (s * (u : ℂ)))
    (Continuous.continuousOn ((hh.continuous.comp continuous_snd).mul
      (Complex.continuous_exp.comp (continuous_fst.mul (Complex.continuous_ofReal.comp continuous_snd)))))
    (fun s _ u hu => by
      show h u * cexp (s * (u : ℂ)) = 0
      rw [image_eq_zero_of_notMem_tsupport hu, zero_mul])
    (fun u => ((differentiable_const (h u)).mul ((differentiable_id.mul_const (u : ℂ)).cexp)).differentiableOn)
  exact differentiableOn_univ.1 h1

theorem continuous_fourier_g {h : ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h) (σ : ℝ) :
    Continuous (𝓕 (g h σ)) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by exact continuous_inner)
    (g_integrable hh hhc σ)

theorem integrable_fourier_g {h : ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h) (σ : ℝ) :
    Integrable (𝓕 (g h σ)) := by
  obtain ⟨C, hC0, hC⟩ := decay hh hhc 2 |σ|
  have hmaj : Integrable fun w : ℝ => C * (1 + ‖w‖) ^ (-(2 : ℝ)) :=
    (integrable_one_add_norm (by norm_num [Module.finrank_self])).const_mul C
  refine hmaj.mono' (continuous_fourier_g hh hhc σ).aestronglyMeasurable (ae_of_all _ fun w => ?_)
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hw : 𝓕 (g h σ) w = ∫ u : ℝ, h u * cexp (((σ : ℂ) + ((-(2 * π * w) : ℝ) : ℂ) * I) * (u : ℂ)) := by
    rw [M_eq_fourier]; congr 1; field_simp
  have h1 := hC σ le_rfl (-(2 * π * w))
  rw [← hw] at h1
  have hp : 0 < (1 + |(-(2 * π * w) : ℝ)|) ^ 2 := by positivity
  have h2 : ‖𝓕 (g h σ) w‖ ≤ C / (1 + |(-(2 * π * w) : ℝ)|) ^ 2 := by
    rw [le_div_iff₀ hp, mul_comm]; exact h1
  refine h2.trans ?_
  rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, Real.norm_eq_abs, Real.rpow_two]
  refine div_le_div_of_nonneg_left hC0 (by positivity) ?_
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  rw [abs_neg, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_two]
  have : |w| ≤ 2 * π * |w| := by
    have hπ3 : (3 : ℝ) < π := Real.pi_gt_three
    nlinarith [abs_nonneg w]
  linarith

theorem inversion {h : ℝ → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h) (σ u : ℝ) :
    h u = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
      ∫ t : ℝ, (∫ v : ℝ, h v * cexp (((σ : ℂ) + (t : ℂ) * I) * (v : ℂ))) *
        cexp (-(((σ : ℂ) + (t : ℂ) * I) * (u : ℂ))) := by
  have hinv := Continuous.fourierInv_fourier_eq (g_contDiff hh σ).continuous (g_integrable hh hhc σ)
    (integrable_fourier_g hh hhc σ)
  have hgu : g h σ u = 𝓕⁻ (𝓕 (g h σ)) u := by rw [hinv]
  rw [Real.fourierInv_eq'] at hgu

  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hsub := Measure.integral_comp_mul_left
    (fun w : ℝ => cexp (↑(2 * π * inner ℝ w u) * I) • 𝓕 (g h σ) w) (-(2 * π)⁻¹)
  have habs : |(-(2 * π)⁻¹ : ℝ)⁻¹| = 2 * π := by
    rw [inv_neg, inv_inv, abs_neg, abs_of_pos (by positivity)]
  rw [habs] at hsub

  have hG : ∀ t : ℝ, cexp (↑(2 * π * inner ℝ (-(2 * π)⁻¹ * t) u) * I) • 𝓕 (g h σ) (-(2 * π)⁻¹ * t) =
      cexp (-((t : ℂ) * I * (u : ℂ))) * ∫ v : ℝ, h v * cexp (((σ : ℂ) + (t : ℂ) * I) * (v : ℂ)) := by
    intro t
    rw [smul_eq_mul, M_eq_fourier, RCLike.inner_apply, conj_trivial]
    have e1 : (-(2 * π)⁻¹ * t : ℝ) = -t / (2 * π) := by field_simp
    have e2 : (2 * π * (u * (-(2 * π)⁻¹ * t)) : ℝ) = -(t * u) := by field_simp
    rw [e2, e1]
    push_cast
    ring_nf
  simp_rw [hG] at hsub

  have hgu' : g h σ u = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
      ∫ t : ℝ, cexp (-((t : ℂ) * I * (u : ℂ))) * ∫ v : ℝ, h v * cexp (((σ : ℂ) + (t : ℂ) * I) * (v : ℂ)) := by
    rw [hgu]
    have h2π : ((2 * π : ℝ)) ≠ 0 := by positivity
    rw [show (∫ w : ℝ, cexp (↑(2 * π * inner ℝ w u) * I) • 𝓕 (g h σ) w) =
      ((2 * π)⁻¹ : ℝ) • ∫ t : ℝ, cexp (-((t : ℂ) * I * (u : ℂ))) * ∫ v : ℝ, h v * cexp (((σ : ℂ) + (t : ℂ) * I) * (v : ℂ))
      from by rw [hsub, smul_smul, inv_mul_cancel₀ h2π, one_smul]]
    rw [Complex.real_smul]

  have hexp : cexp ((σ : ℂ) * (u : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hh_eq : h u = g h σ u * cexp (-((σ : ℂ) * (u : ℂ))) := by
    rw [g_apply, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  rw [hh_eq, hgu', mul_assoc, ← integral_mul_const]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show cexp (-((t : ℂ) * I * (u : ℂ))) * (∫ v : ℝ, h v * cexp (((σ : ℂ) + (t : ℂ) * I) * (v : ℂ))) *
      cexp (-((σ : ℂ) * (u : ℂ))) = _
  rw [mul_comm (cexp _) (∫ v : ℝ, _), mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  ring

end MPW

theorem solution
    (h : ℝ → ℂ) (_hh : ContDiff ℝ (⊤ : ℕ∞) h) (_hhc : HasCompactSupport h) :
    Differentiable ℂ (fun s : ℂ => ∫ u : ℝ, h u * Complex.exp (s * (u : ℂ))) ∧
    (∀ (n : ℕ) (σ₀ : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ → ∀ t : ℝ,
      (1 + |t|) ^ n * ‖∫ u : ℝ, h u * Complex.exp (((σ' : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))‖ ≤ C) ∧
    (∀ (σ' u : ℝ), h u = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
      ∫ t : ℝ, (∫ v : ℝ, h v * Complex.exp (((σ' : ℂ) + (t : ℂ) * Complex.I) * (v : ℂ))) *
        Complex.exp (-(((σ' : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ)))) :=
  ⟨MPW.differentiable_M _hh _hhc, fun n σ₀ => MPW.decay _hh _hhc n σ₀, fun σ' u => MPW.inversion _hh _hhc σ' u⟩

end S_MellinPaleyWiener_differentiable_and_forall_decay_and_inversion_of_contDiff_of_hasCompactSupport
end P2MW
export P2MW.S_MellinPaleyWiener_differentiable_and_forall_decay_and_inversion_of_contDiff_of_hasCompactSupport (solution)
