-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_smooth_weak_limit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:06:21.271586+00:00
-- url     : https://prove2.me/submissions/43fcb7fc-83a0-457a-8d6a-35d53afcf89d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Theorems.Thm_GroundTheory_Automorphic_WeakLimit_integral_fourier_mul_eq
import Theorems.Thm_GroundTheory_Automorphic_WeakLimit_integral_fourierInv_mul_eq
import Theorems.Thm_GroundTheory_Automorphic_WeakLimit_norm_fourier_le
import Theorems.Thm_GroundTheory_Automorphic_WeakLimit_continuous_fourier_of_integrable
import Theorems.Thm_GroundTheory_Automorphic_WeakLimit_exists_smooth_near

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Filter Topology Set
open scoped FourierTransform ContDiff
namespace GroundTheory.Automorphic
theorem _root_.solution {K : ℕ → ℝ → ℝ} {a b : ℝ} (hKi : ∀ N, Integrable (K N))
    (hK0 : ∀ N t, 0 ≤ K N t) (hK1 : ∀ N, ∫ t, K N t ≤ 1)
    (hKs : ∀ N, Function.support (K N) ⊆ Icc a b)
    (hconv : ∀ ξ : ℝ, ∃ l : ℂ, Tendsto (fun N => 𝓕 (fun t => (K N t : ℂ)) ξ) atTop (𝓝 l))
    (hdecay : ∀ m : ℕ, ∃ C N₀, ∀ N ≥ N₀, ∀ ξ : ℝ,
      ‖𝓕 (fun t => (K N t : ℂ)) ξ‖ ≤ C * (1 + |ξ|) ^ (-(m : ℝ))) :
    ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧ tsupport g ⊆ Icc a b ∧
      ∀ ψ : ℝ → ℂ, Continuous ψ →
        Tendsto (fun N => ∫ t, ψ t * K N t) atTop (𝓝 (∫ t, ψ t * g t)) := by
  set Kc : ℕ → ℝ → ℂ := fun N t => (K N t : ℂ) with hKc
  have hKci : ∀ N, Integrable (Kc N) := fun N => (hKi N).ofReal
  have hKn : ∀ N ξ, ‖𝓕 (Kc N) ξ‖ ≤ 1 := by
    intro N ξ
    refine (WeakLimit.norm_fourier_le _ ξ).trans ?_
    simp only [Kc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 N _)]
    exact hK1 N
  choose Φ hΦ using hconv
  have hΦd : ∀ m : ℕ, ∃ C, ∀ ξ, ‖Φ ξ‖ ≤ C * (1 + |ξ|) ^ (-(m : ℝ)) := by
    intro m
    obtain ⟨C, N₀, hC⟩ := hdecay m
    exact ⟨C, fun ξ => le_of_tendsto ((hΦ ξ).norm) (eventually_atTop.2 ⟨N₀, fun N hN => hC N hN ξ⟩)⟩
  have hΦm : AEStronglyMeasurable Φ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun N => (WeakLimit.continuous_fourier_of_integrable (hKci N)).aestronglyMeasurable)
      (ae_of_all _ hΦ)
  have hΦint : ∀ n : ℕ, Integrable (fun ξ : ℝ => ‖ξ‖ ^ n * ‖Φ ξ‖) := by
    intro n
    obtain ⟨C, hC⟩ := hΦd (n + 2)
    have hI : Integrable (fun ξ : ℝ => C * (1 + ‖ξ‖) ^ (-(2 : ℝ))) :=
      (integrable_one_add_norm (by norm_num)).const_mul C
    refine hI.mono' ((continuous_norm.pow n).aestronglyMeasurable.mul hΦm.norm)
      (ae_of_all _ fun ξ => ?_)
    have h1 : 0 < 1 + |ξ| := by positivity
    rw [norm_mul, norm_pow, norm_norm, norm_norm, Real.norm_eq_abs]
    calc |ξ| ^ n * ‖Φ ξ‖ ≤ (1 + |ξ|) ^ n * (C * (1 + |ξ|) ^ (-((n + 2 : ℕ) : ℝ))) :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (by linarith) n) (hC ξ) (norm_nonneg _)
            (by positivity)
      _ = C * (1 + |ξ|) ^ (-(2 : ℝ)) := by
          rw [← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add h1]
          congr 2; push_cast; ring
  have hΦi : Integrable Φ := (integrable_norm_iff hΦm).1 (by simpa using hΦint 0)
  set g : ℝ → ℂ := 𝓕⁻ Φ with hgdef
  have hg : ContDiff ℝ ∞ g := by
    rw [hgdef, Real.fourierInv_eq_fourier_comp_neg]
    exact Real.contDiff_fourier fun n _ => by simpa using (hΦint n).comp_neg

  have hsmooth : ∀ ψ : ℝ → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Tendsto (fun N => ∫ t, ψ t * Kc N t) atTop (𝓝 (∫ t, ψ t * g t)) := by
    intro ψ hψ hψc
    let ψS := hψc.toSchwartzMap hψ
    have hψi : Integrable ψ := hψ.continuous.integrable_of_hasCompactSupport hψc
    have hθi : Integrable (𝓕⁻ ψ) := by
      have := (𝓕⁻ ψS).integrable (μ := volume)
      rwa [SchwartzMap.fourierInv_coe] at this
    have hFψ : Integrable (𝓕 ψ) := by
      have := (𝓕 ψS).integrable (μ := volume)
      rwa [SchwartzMap.fourier_coe] at this
    have hinv : 𝓕 (𝓕⁻ ψ) = ψ := hψ.continuous.fourier_fourierInv_eq hψi hFψ
    have e1 : ∀ N, ∫ t, ψ t * Kc N t = ∫ ξ, 𝓕⁻ ψ ξ * 𝓕 (Kc N) ξ := by
      intro N
      conv_lhs => rw [← hinv]
      exact WeakLimit.integral_fourier_mul_eq hθi (hKci N)
    have e2 : ∫ t, ψ t * g t = ∫ ξ, 𝓕⁻ ψ ξ * Φ ξ :=
      (WeakLimit.integral_fourierInv_mul_eq hψi hΦi).symm
    simp_rw [e1, e2]
    refine tendsto_integral_of_dominated_convergence (fun ξ => ‖𝓕⁻ ψ ξ‖) (fun N => ?_)
      hθi.norm (fun N => ae_of_all _ fun ξ => ?_) (ae_of_all _ fun ξ => (hΦ ξ).const_mul _)
    · exact hθi.aestronglyMeasurable.mul
        (WeakLimit.continuous_fourier_of_integrable (hKci N)).aestronglyMeasurable
    · rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hKn N ξ)

  have hgi : LocallyIntegrable g := hg.continuous.locallyIntegrable
  have hsupp : Function.support g ⊆ Icc a b := by
    have hae : ∀ᵐ x, x ∈ (Icc a b)ᶜ → g x = 0 := by
      refine isClosed_Icc.isOpen_compl.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (hgi.locallyIntegrableOn _) fun φ hφ hφc hφs => ?_
      have hlim := hsmooth (fun x => (φ x : ℂ)) (Complex.ofRealCLM.contDiff.comp hφ)
        (hφc.comp_left Complex.ofReal_zero)
      have h0 : ∀ N, ∫ t, (φ t : ℂ) * Kc N t = 0 := by
        intro N
        refine integral_eq_zero_of_ae (ae_of_all _ fun t => ?_)
        by_cases ht : t ∈ Icc a b
        · have : φ t = 0 := image_eq_zero_of_notMem_tsupport fun h' => hφs h' ht
          simp [this]
        · have : K N t = 0 := Function.notMem_support.1 fun h' => ht (hKs N h')
          simp [Kc, this]
      simp_rw [h0] at hlim
      simp_rw [Complex.real_smul]
      exact tendsto_nhds_unique hlim tendsto_const_nhds
    intro x hx
    by_contra hxI
    have hopen : IsOpen ((Icc a b)ᶜ ∩ Function.support g) :=
      isClosed_Icc.isOpen_compl.inter hg.continuous.isOpen_support
    have hnull : volume ((Icc a b)ᶜ ∩ Function.support g) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      exact hae.mono fun y hy hy' => hy'.2 (hy hy'.1)
    exact (hopen.measure_ne_zero volume ⟨x, hxI, hx⟩) hnull
  refine ⟨g, hg, closure_minimal hsupp isClosed_Icc, fun ψ hψ => ?_⟩
  have hgc : HasCompactSupport g :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) (closure_minimal hsupp isClosed_Icc)
  have hIK : ∀ φ : ℝ → ℂ, Continuous φ → ∀ N, Integrable (fun t => φ t * Kc N t) := by
    intro φ hφ N
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hφ.continuousOn
    refine ((hKi N).const_mul B).mono' (hφ.aestronglyMeasurable.mul (hKci N).aestronglyMeasurable)
      (ae_of_all _ fun t => ?_)
    by_cases ht : t ∈ Icc a b
    · rw [norm_mul]
      simp only [Kc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 N t)]
      exact mul_le_mul_of_nonneg_right (hB t ht) (hK0 N t)
    · have : K N t = 0 := Function.notMem_support.1 fun h' => ht (hKs N h')
      simp [Kc, this]
  have hIg : ∀ φ : ℝ → ℂ, Continuous φ → Integrable (fun t => φ t * g t) := fun φ hφ =>
    (hφ.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  set L := ∫ t, ‖g t‖ with hLdef
  have hL : 0 ≤ L := integral_nonneg fun _ => norm_nonneg _
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set η := δ / (4 * (L + 2)) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨ψ', hψ', hψ'c, hψψ'⟩ := WeakLimit.exists_smooth_near a b hψ hηpos
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 (hsmooth ψ' hψ' hψ'c) (δ / 2) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have hdiffK : ‖(∫ t, ψ t * Kc N t) - ∫ t, ψ' t * Kc N t‖ ≤ η := by
    rw [← integral_sub (hIK ψ hψ N) (hIK ψ' hψ'.continuous N)]
    refine (norm_integral_le_of_norm_le ((hKi N).const_mul η) (ae_of_all _ fun t => ?_)).trans ?_
    · rw [← sub_mul, norm_mul]
      by_cases ht : t ∈ Icc a b
      · simp only [Kc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 N t)]
        exact mul_le_mul_of_nonneg_right (hψψ' t ht) (hK0 N t)
      · have : K N t = 0 := Function.notMem_support.1 fun h' => ht (hKs N h')
        simp [Kc, this]
    · rw [integral_const_mul]
      exact mul_le_of_le_one_right hηpos.le (hK1 N)
  have hdiffg : ‖(∫ t, ψ' t * g t) - ∫ t, ψ t * g t‖ ≤ η * L := by
    rw [← integral_sub (hIg ψ' hψ'.continuous) (hIg ψ hψ), hLdef, ← integral_const_mul]
    refine norm_integral_le_of_norm_le ((hg.continuous.norm.integrable_of_hasCompactSupport hgc.norm).const_mul η) (ae_of_all _ fun t => ?_)
    rw [← sub_mul, norm_mul]
    by_cases ht : t ∈ Icc a b
    · rw [norm_sub_rev]
      exact mul_le_mul_of_nonneg_right (hψψ' t ht) (norm_nonneg _)
    · have : g t = 0 := Function.notMem_support.1 fun h' => ht (hsupp h')
      simp [this]
  have hmid : dist (∫ t, ψ' t * Kc N t) (∫ t, ψ' t * g t) < δ / 2 := hN₀ N hN
  rw [dist_eq_norm] at hmid ⊢
  have h3 : ‖(∫ t, ψ t * Kc N t) - ∫ t, ψ t * g t‖ ≤
      ‖(∫ t, ψ t * Kc N t) - ∫ t, ψ' t * Kc N t‖ +
        ‖(∫ t, ψ' t * Kc N t) - ∫ t, ψ' t * g t‖ + ‖(∫ t, ψ' t * g t) - ∫ t, ψ t * g t‖ :=
    (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (by
      linarith [norm_sub_le_norm_sub_add_norm_sub (∫ t, ψ' t * Kc N t) (∫ t, ψ' t * g t)
        (∫ t, ψ t * g t)])
  have h4 : η + η * L < δ / 2 := by
    have hpos : 0 < 4 * (L + 2) := by positivity
    have h5 : η * (4 * (L + 2)) = δ := by rw [hη]; field_simp
    nlinarith [mul_nonneg hηpos.le hL]
  show ‖(∫ t, ψ t * Kc N t) - ∫ t, ψ t * g t‖ < δ
  linarith
end GroundTheory.Automorphic
